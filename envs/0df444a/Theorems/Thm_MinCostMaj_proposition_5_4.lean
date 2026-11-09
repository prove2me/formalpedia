-- Prove2me | Theorems.Thm_MinCostMaj_proposition_5_4
-- name    : MinCostMaj.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:20.566969+00:00
-- url     : https://prove2.me/theorems/f898512e-7794-49bd-8803-6ecceae56398
-- title:
--   Proposition 5.4 — the truncated instance has a solution
-- statement:
--   Let $\mathbf A$ be a finite relational structure with a conservative majority polymorphism that satisfies the tractable-side condition of Theorem 3.2 (for every ac-leq-cycle pair $(I',J')$ over the normalized structure, $I'$ has a solution). Let $J$ be a simplified instance over the normalized structure on finitely many variables that is (2,3)-consistent with all potatoes nonempty, let $(\lambda_x,\lambda_{xy})$ be a feasible solution of the BLP of $J$, and let $(t_i)_{i\ge1}$ be any threshold sequence with $t_i\in[2^{-i},2^{-(i-1)}]$. Then the truncated instance $I$, with potatoes
--   $$A^I_v=\{a\in A^J_v:\lambda_v(a)\ge t_{L(v)}\}$$
--   and the constraints of $J$, has a solution: some $\alpha$ satisfies $\alpha(v)\in A^I_v$ for all $v$ and $(\alpha(x),\alpha(y))\in R^J_{xy}$ for all $x,y$.
--
--   So the rounding never fails, and any solution of $I$ may be returned.
--
--   Differences from the source:
--   - reading: Proposition 5.4 printed without hypotheses → the standing assumptions of §5 and Appendix C made explicit: conservative majority polymorphism, the tractable-side condition of Theorem 3.2, J simplified, over the normalized structure, (2,3)-consistent with nonempty potatoes; reason: the proof (Appendix C, pp.25–27) uses exactly these; J's relations "belong to A by our convention in Section 3" (p.27)
--   - generalization: λ an optimal BLP solution, t sampled → any feasible BLP solution and every threshold sequence with t_i ∈ [2^{−i}, 2^{−(i−1)}]; reason: the proof uses only feasibility and the range of the thresholds; the sampled optimal case is a special case
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Proposition 5.4, p.11 (PDF p.12); proof Appendix C, pp.22–27

import Mathlib
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_HasConsMajPol
import Definitions.Def_MinCostMaj_normBin
import Definitions.Def_MinCostMaj_SimpInst
import Definitions.Def_MinCostMaj_Levels

namespace MinCostMaj

/-- **Proposition 5.4**, p.11 (PDF p.12; proof Appendix C, pp.22–27).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Proposition 5.4, p.11: "The truncated instance I has a solution."

Standing assumptions of §5 and Appendix C, made explicit: `A` has a conservative majority
polymorphism and satisfies the tractable-side condition of Theorem 3.2 (every ac-leq-cycle pair of
instances over the normalized structure has a solvable smaller instance); `J` is a simplified
instance (one relation `R_xy` per ordered pair, `R_yx = −R_xy`, `R_xx` diagonal) over the
normalized structure that is (2,3)-consistent with every potato nonempty (the output of the
preprocessing); `(λ₁, λ₂)` is a feasible BLP solution of `J`; `t` is a threshold sequence with
`tᵢ ∈ [2^{−i}, 2^{−(i−1)}]` for `i ≥ 1`. Then some assignment takes every variable `v` into its
truncated potato `A^I_v = {a ∈ A^J_v : λᵥ(a) ≥ t_{L(v)}}` and satisfies every `R_xy`.

**Formalization Note.** The proof uses only feasibility of `λ` (not optimality) and holds for
every threshold sequence in the sampling range, so both are universally quantified. The relations
of `J` "belong to A by our convention in Section 3" (p.27): they lie in `normBin A`. -/
theorem proposition_5_4 {d : ℕ} (A : Struct d) (hA : HasConsMajPol A) (hT : TractCond A)
    {n : ℕ} (R : Fin n → Fin n → Set (Fin d × Fin d)) (hR : IsSimplified R)
    (hN : ∀ x y, R x y ∈ normBin A) (h23 : Is23Consistent R)
    (hne : ∀ x, (simpPot R x).Nonempty) (lam₁ : Fin n → Fin d → ℝ)
    (lam₂ : Fin n → Fin n → Fin d × Fin d → ℝ) (hlp : IsBLPFeasible R lam₁ lam₂)
    (t : ℕ → ℝ) (ht : ∀ i, 1 ≤ i → ((1 : ℝ) / 2) ^ i ≤ t i ∧ t i ≤ 2 * ((1 : ℝ) / 2) ^ i) :
    ∃ α : Fin n → Fin d, (∀ v, α v ∈ truncPot (simpPotF R v) (lam₁ v) t) ∧
      ∀ x y, (α x, α y) ∈ R x y := by sorry

end MinCostMaj
