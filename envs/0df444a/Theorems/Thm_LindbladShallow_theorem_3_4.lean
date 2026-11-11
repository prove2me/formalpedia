-- Prove2me | Theorems.Thm_LindbladShallow_theorem_3_4
-- name    : LindbladShallow.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:20:50.166736+00:00
-- url     : https://prove2.me/theorems/4b4edc1b-4084-4a17-a86e-de11e9da8a4f
-- title:
--   Theorem 3.4 — shared-environment locality
-- statement:
--   Fix a valid input, a segment of $M\ge1$ periods with step $h>0$, nested sets $\mathcal T_0\subseteq\mathcal T_1$ of active terms and a region $\Omega$. Let $U_i$ be the collision circuit of $\mathcal T_i$, $U_{i,\Omega}$ its restriction to occurrences with support in $\Omega$, $E_0$ the shared vacuum initialization and
--   $$\mathcal M=E_0^\dagger U_1^\dagger U_{1,\Omega}U_{0,\Omega}^\dagger U_0E_0.$$
--   On $B=\{(e,m):e\in\mathcal T_1,0\le m<M\}$ (Hamiltonian labels included), with $X_{(e,m)}=X_e$, let $\omega_b=64h\lambda_b$, $S=\{(e,m):e\in\mathcal T_1\setminus\mathcal T_0\}$, $C=\{(e,m):X_e\not\subseteq\Omega\}$ and $d_w,W_S$ as in Lemma 3.3. Suppose $h\lambda_b\le1$ for every label, $6d_w<1$, and every connected set meeting $S$ and $C$ has at least $m_*\ge1$ vertices. With $\zeta=W_S(6d_w)^{m_*-1}/(1-6d_w)$,
--   $$\|I-\mathcal M\|\le e^\zeta-1,\qquad \big\|(U_1-U_{1,\Omega}U_{0,\Omega}^\dagger U_0)E_0\big\|\le\sqrt{2(e^\zeta-1)}.$$
--
--   This locality estimate for the joint system–environment evolution replaces the reversibility that the Haah–Hastings–Kothari–Low decomposition needs; it drives the spatial decomposition of Corollary 3.5.
--
--   Differences from the source:
--   - encoding: active term sets → finite sets of retained term indices; reason: preprocessing removes the other terms; removed terms have no collision gates
--   - encoding: a region Ω → any set of sites; only X_e ⊆ Ω is used; reason: Ω and Ω ∩ Λ give the same restriction since supports lie in Λ
--   - encoding: restriction replaces gates by identities preserving positions and bath labels → restricted words drop those occurrences; bath registers are indexed by all jump labels of the segment; reason: identity gates do not change the product
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 3.4, p.16; setting Eq. (8), pp.13–14

import Mathlib
import Definitions.Def_LindbladShallow_lam
import Definitions.Def_LindbladShallow_collision
import Definitions.Def_LindbladShallow_activity

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Theorem 3.4** (Shared-environment locality; arXiv:2610.05362, held version
sha256 8f4637ef…, p.16, with the setting of Eq. (8), pp.13–14). Fix one segment of `M` collision
periods of step `h > 0`, nested sets `T₀ ⊆ T₁` of active (retained) terms, and a region `Ω`. Let
`U_i` be the collision circuit of `T_i`, `U_{i,Ω}` its restriction to the occurrences whose support
lies in `Ω`, `E₀` the shared vacuum initialization, and `M := E₀†U₁†U_{1,Ω}U_{0,Ω}†U₀E₀` (8).
On the occurrence labels `B = {(e, m) : e ∈ T₁, 0 ≤ m < M}` (Hamiltonian labels included) with
supports `X_{(e,m)} = X_e`, put `ω_b = 64hλ_b`, `S := {(e, m) : e ∈ T₁ \ T₀}`,
`C := {(e, m) : X_e ⊄ Ω}`, `d_w`, `W_S` as in Lemma 3.3. Suppose `hλ_b ≤ 1` for every label,
`6d_w < 1`, and every connected vertex set meeting `S` and `C` has at least `m∗ ≥ 1` vertices.
With `ζ = W_S(6d_w)^{m∗−1}/(1 − 6d_w)`,
`‖I − M‖ ≤ e^ζ − 1` and `‖(U₁ − U_{1,Ω}U_{0,Ω}†U₀)E₀‖ ≤ √(2(e^ζ − 1))` (10).

**Formalization Note** Operator norms are the spectral norm on the whole system ⊗ environment
input of `E₀` (system input arbitrary; an untouched reference does not change an operator norm).
`Ω` is any set of sites; only `X_e ⊆ Ω` matters. -/
theorem theorem_3_4 {P : Params} (I : Instance P) (hI : I.Valid) (M : ℕ) (hM : 1 ≤ M)
    (h : ℝ) (hh : 0 < h) (T0 T1 : Finset (Fin I.nT)) (hT : T0 ⊆ T1)
    (hret : ∀ e ∈ T1, (I.term e).Retained) (Ω : Set (Site P)) (mstar : ℕ) (hm : 1 ≤ mstar) :
    let B : Finset (Fin I.nT × Fin M) := T1 ×ˢ Finset.univ
    let X : Fin I.nT × Fin M → Finset (Site P) := fun b => (I.term b.1).supp.toFinset
    let ω : Fin I.nT × Fin M → ℝ := fun b => 64 * h * lamE I b.1
    let S : Finset (Fin I.nT × Fin M) := B.filter fun b => b.1 ∉ T0
    let Cut : Finset (Fin I.nT × Fin M) :=
      open Classical in B.filter fun b => ¬ ∀ x ∈ (I.term b.1).supp, x ∈ Ω
    let U0 := collU I M h (· ∈ T0) Set.univ
    let U1 := collU I M h (· ∈ T1) Set.univ
    let U0Ω := collU I M h (· ∈ T0) Ω
    let U1Ω := collU I M h (· ∈ T1) Ω
    let Mop : Matrix (Sys I) (Sys I) ℂ :=
      Matrix.conjTranspose (E0 I M) * Matrix.conjTranspose U1 * U1Ω *
        Matrix.conjTranspose U0Ω * U0 * E0 I M
    let ζ := zeta B S X ω mstar
    (∀ b ∈ B, h * lamE I b.1 ≤ 1) →
    6 * dwt B X ω < 1 →
    (∀ F ⊆ B, IsConnSet X F → (F ∩ S).Nonempty → (F ∩ Cut).Nonempty → mstar ≤ F.card) →
    opNorm (1 - Mop) ≤ Real.exp ζ - 1 ∧
      opNorm ((U1 - U1Ω * Matrix.conjTranspose U0Ω * U0) * E0 I M) ≤
        Real.sqrt (2 * (Real.exp ζ - 1)) := by sorry

end LindbladShallow
