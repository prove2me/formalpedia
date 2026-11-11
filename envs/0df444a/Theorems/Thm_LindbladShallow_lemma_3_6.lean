-- Prove2me | Theorems.Thm_LindbladShallow_lemma_3_6
-- name    : LindbladShallow.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:19:20.590183+00:00
-- url     : https://prove2.me/theorems/7a094947-e758-4015-a2a3-e9431e2fe367
-- title:
--   Lemma 3.6 — occupation moment
-- statement:
--   Let $U_1,\dots,U_m$ be unitaries on a system and a family of baths, each touching at most one bath, and $Y=U_m\cdots U_1E_0$, where $E_0$ initializes every bath to vacuum. For a counted bath set $\mathcal B_{\mathrm{cat}}$, $N_{\mathrm{cat}}=\sum_{b\in\mathcal B_{\mathrm{cat}}}P_b$ and $a_b=\sum_{j\text{ touches }b}\|[P_b,U_j]\|$, for every $F\subseteq\mathcal B_{\mathrm{cat}}$ and $z\ge1$:
--   $$\|P_FY\|\le\prod_{b\in F}a_b,\qquad Y^\dagger z^{N_{\mathrm{cat}}}Y\preceq\prod_b[1+(z-1)a_b^2]\,I,\qquad Y^\dagger P_bz^{N_{\mathrm{cat}}-P_b}Y\preceq a_b^2\prod_{c\ne b}[1+(z-1)a_c^2]\,I.$$
--   If each bath is visited at most $\nu$ times by normalized physical collision gates whose total interaction weight $\sum_jh_j\lambda_j$ is at most $\Sigma$, then $\sum_ba_b^2\le\nu\Sigma/4$.
--
--   These moment bounds control how many baths are occupied on the inputs of the local solver.
--
--   Differences from the source:
--   - generalization: each elementary gate touches at most one bath (acts as identity on the others) → each gate fails to commute with P_b for at most one bath b; reason: a gate acting as the identity on a bath commutes with its P_b, so the Lean hypothesis is weaker; the proof uses only the commutation
--   - generalization: normalized gates (β² ≥ 4‖J‖_F²) → 4‖J‖² ≤ λ with the operator norm, h ≥ 0; reason: the Frobenius normalization implies the operator-norm one
--   - generalization: total interaction weight of the collision gates at most Σ → the weight Σ h_jλ_j of the jump gates at most Σ; reason: Hamiltonian gates add nonnegative weight, so this hypothesis is weaker
--   - encoding: E₀ initializes every counted bath; B_cat a fixed local set → E₀ initializes every bath; B_cat any finite subset of the baths; reason: uncounted registers can be absorbed into the system type
--   - encoding: z^{N_cat}, P_b z^{N_cat − P_b} → diagonal matrices in the bath basis with entries z^{#occupied}; reason: these operators are diagonal in that basis
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 3.6, p.19, Eqs. (12)–(14)

import Mathlib
import Definitions.Def_LindbladShallow_occupation

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Lemma 3.6** (Occupation moment; arXiv:2610.05362, held version sha256 8f4637ef…, p.19).
Let `U_1, …, U_m` be unitaries on system ⊗ baths, each touching at most one bath, and
`Y = U_m ⋯ U_1E₀` with `E₀` initializing every counted bath to vacuum. For the counted bath set
`B_cat`, `N_cat = Σ_{b ∈ B_cat} P_b`, and `a_b = Σ_{j touches b} ‖[P_b, U_j]‖`, for every
`F ⊆ B_cat` and `z ≥ 1`: (12) `‖P_F Y‖ ≤ ∏_{b∈F} a_b`; (13) `Y† z^{N_cat} Y ⪯ ∏_b [1 + (z−1)a_b²] I`;
(14) `Y† P_b z^{N_cat−P_b} Y ⪯ a_b² ∏_{c≠b} [1 + (z−1)a_c²] I`. If each bath is visited at most `ν`
times and the total interaction weight `Σ_j h_jλ_j` of the normalized physical collision gates is
at most `Σ`, then `Σ_b a_b² ≤ νΣ/4`.

**Formalization Note** The baths are all counted (uncounted registers can be absorbed into the
system `σ`); `B_cat` is any finite set of them. "Touches" is `[P_b, U] ≠ 0`; a gate acting as the
identity on all but one bath touches at most that one. For the last clause the gates are
Hamiltonian gates on the system and forward/adjoint jump Cayley gates `V_{J,h}^{±1}` on one bath,
normalized by `4‖J‖² ≤ λ` (implied by the paper's `β² ≥ 4‖J‖_F²`), `h ≥ 0`; a visit of `b` is a
jump gate on `b`, and the weight sums over jump gates (Hamiltonian gates add nonnegative weight, so
this is the weaker hypothesis). -/
theorem lemma_3_6 {σ β : Type*} [Fintype σ] [DecidableEq σ] [Fintype β] [DecidableEq β] {d : ℕ}
    (Bcat : Finset β) :
    (∀ Us : List (Matrix (OccSp σ β d) (OccSp σ β d) ℂ),
      (∀ U ∈ Us, U ∈ Matrix.unitaryGroup (OccSp σ β d) ℂ) →
      (∀ U ∈ Us, ∀ b c, Touches U b → Touches U c → b = c) →
      OccBounds Bcat (aBound Us) (orderedProd Us * vacOcc)) ∧
    (∀ (gs : List (CollGate σ β d)) (ν : ℕ) (Sig : ℝ),
      (∀ g ∈ gs, ∀ b J h lam adj, g = .jump b J h lam adj → 0 ≤ h ∧ 4 * opNorm J ^ 2 ≤ lam) →
      (∀ b, (gs.filter fun g => match g with
          | .jump b' _ _ _ _ => decide (b' = b)
          | .ham _ => false).length ≤ ν) →
      (gs.map fun g => match g with
          | .jump _ _ h lam _ => h * lam
          | .ham _ => 0).sum ≤ Sig →
      ∑ b ∈ Bcat, aBound (gs.map CollGate.mat) b ^ 2 ≤ ν * Sig / 4) := by sorry

end LindbladShallow
