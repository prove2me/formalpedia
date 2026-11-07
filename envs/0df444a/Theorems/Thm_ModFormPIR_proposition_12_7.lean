-- Prove2me | Theorems.Thm_ModFormPIR_proposition_12_7
-- name    : ModFormPIR.proposition_12_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:42.386772+00:00
-- url     : https://prove2.me/theorems/0a9ccdae-623f-4b48-9bdb-f6624b6202fa
-- title:
--   Proposition 12.7 with Proposition 12.6 and duality (41), pp.67–68 — the symmetrized witness
-- statement:
--   Let $q\mid d$, $\mathcal A\subseteq\mathbb Z_q$, and let $T\subseteq\mathbb Z_q^d$ be closed under adding $b\mathbf 1$, with $S=\{z+ce_1:z\in T,c\in\mathbb Z_q\}$. For any $X\subseteq\mathbb Z_q^d$ (in particular $X=S_d(\vartheta,\nu)$): if no quadratic-phase delta expansion has support in $X\times\mathcal A$, there is $\alpha$ with
--   $$\alpha_0=1,\qquad\sum_x\alpha_x\zeta_q^{a\langle x,x\rangle+\langle x,z\rangle}=0\quad\forall a\in\mathcal A,z\in X.\tag{41}$$
--   For any $\alpha$ with (41) on $X=S$, some $\alpha^{(J)}_0\ne0$, and for every such $J$, the vector $\beta_x=\alpha^{(J)}_x/\alpha^{(J)}_0$ satisfies
--   $$\beta_0=1,\quad\beta_x=0\text{ if }\sum_ix_i\ne0,\quad\beta_x=\beta_{x+\mathbf 1},\quad\sum_x\beta_x\zeta_q^{a\langle x,x\rangle+\langle x,z\rangle}=0\ \ \forall a\in\mathcal A,z\in T.$$
--
--   This is the first step of the proof of Theorem 12.2: it puts the dual witness into the symmetric form the modular-forms argument needs.
--
--   Differences from the source:
--   - generalization: duality (41) on S_d(ϑ,ν); Proposition 12.7 for α with (41) on S_d(ϑ,ν), T = T_d(ϑ,ν), 𝒜 of size s → duality for every support set X; Proposition 12.7 for α with (41) on S, the first-coordinate thickening of any T closed under +b𝟏, and any 𝒜; reason: the duality is linear algebra valid for any X (X = S_d is an instance); the symmetrization uses only these properties of T and S, and the printed case is recovered as T_d is shift-closed and its first-coordinate thickening lies inside S_d
--   - encoding: no expansion over ℚ(ζ_q) → no expansion over ℂ with γ = ζ_q; reason: the proof dualizes in ℂ^{ℤ_q^d}; a linear system over ℚ(ζ_q) solvable over ℂ is solvable over ℚ(ζ_q)
--   - encoding: "Fix J such that α^{(J)}_0 ≠ 0" → existence of J (Proposition 12.6) and every such J; reason: the printed fix is meaningful through Proposition 12.6
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definition 12.5, Propositions 12.6, 12.7, (41)–(45), pp.67–68 (PDF pp.71–72)

import Mathlib
import Definitions.Def_ModFormPIR_Witness

open Matrix

set_option autoImplicit false

namespace ModFormPIR

/-- **Proposition 12.7** with Proposition 12.6 and the duality step (41), pp.67–68. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For any set `X ⊆ ℤ_q^d` (in particular `X = S_d(ϑ,ν)`): if no expansion with support in `X × 𝒜` exists, a vector `α` with `α_0 = 1` and (41) on `X` exists. For every such `α` some `α^{(J)}_0` is nonzero, and for each such `J`, `β = α^{(J)}/α^{(J)}_0` satisfies
(42)–(45).

**Formalization Note.** Printed under `S = S_d(ϑ,ν)`, `T = T_d(ϑ,ν)`, a case with no witness by Theorem 12.2. Here `T` is any subset of `ℤ_q^d` closed under `+b𝟏`, and `S = {z + c e_1 : z ∈ T, c ∈ ℤ_q}`, the part of `S_d` the proof uses; this
contains the printed case, by restricting `α` from `S_d` to `S`. The duality clause is stated for every support set `X`, so it gives (41) on `S_d` itself. The expansion is over `ℂ` with `γ = ζ_q`; a linear system over `ℚ(ζ_q)` solvable over `ℂ` is solvable over `ℚ(ζ_q)`, so absence over `ℂ` is absence over `ℚ(ζ_q)`. -/
theorem proposition_12_7 (q d : ℕ) [NeZero q] (hq : q.Prime) (hodd : Odd q) (hd : 1 ≤ d)
    (hqd : q ∣ d) (𝒜 : Finset (ZMod q)) (T : Set (Fin d → ZMod q))
    (hT : ∀ z ∈ T, ∀ b : ZMod q, (fun i => z i + b) ∈ T) (i₀ : Fin d) (hi₀ : (i₀ : ℕ) = 0)
    (S : Set (Fin d → ZMod q)) (hS : S = {y | ∃ z ∈ T, ∃ c : ZMod q, y = z + Pi.single i₀ c}) :
    (∀ X : Set (Fin d → ZMod q),
      (¬ ∃ c : (Fin d → ZMod q) → ZMod q → ℂ, IsDeltaExpansion (zeta q) c ∧
          HasSupport c X (𝒜 : Set (ZMod q))) →
      ∃ α : (Fin d → ZMod q) → ℂ, α 0 = 1 ∧ ∀ a ∈ 𝒜, IsOrthogonalOn α a X) ∧
    ∀ α : (Fin d → ZMod q) → ℂ, α 0 = 1 → (∀ a ∈ 𝒜, IsOrthogonalOn α a S) →
      (∃ J : ZMod q, alphaJ i₀ α J 0 ≠ 0) ∧
      ∀ J : ZMod q, alphaJ i₀ α J 0 ≠ 0 →
        IsNormalizedWitness (fun x => alphaJ i₀ α J x / alphaJ i₀ α J 0) ∧
        ∀ a ∈ 𝒜, IsOrthogonalOn (fun x => alphaJ i₀ α J x / alphaJ i₀ α J 0) a T := by sorry

end ModFormPIR
