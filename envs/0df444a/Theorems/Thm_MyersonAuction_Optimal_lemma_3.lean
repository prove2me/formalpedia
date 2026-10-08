-- Prove2me | Theorems.Thm_MyersonAuction_Optimal_lemma_3
-- name    : MyersonAuction.Optimal.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:46:32.782687+00:00
-- url     : https://prove2.me/theorems/8441dc4a-cdad-4c00-bd6c-2a99f605d9b1
-- title:
--   Lemma 3 — maximizing virtual surplus gives an optimal auction
-- statement:
--   Suppose an allocation rule $p$ maximizes expected virtual surplus among the allocation rules satisfying the single-object probability constraint and weak monotonicity of every interim win probability. Give bidder $i$ the envelope payment
--
--   $$x_i(t)=p_i(t)v_i(t)-\int_{a_i}^{t_i}p_i(t_{-i},s)\,ds.$$
--
--   Then $(p,x)$ is a feasible mechanism and maximizes the seller’s expected utility over all feasible direct mechanisms. This is the source’s reduction from optimal mechanisms to an allocation problem.
--
--   **Formalization Note** The competing allocations and the proposed allocation are required to have integrable allocation functions and report sections.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), p. 64, Lemma 3, eqs. (4.7)–(4.8)

import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

theorem lemma_3 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x : Outcome ι)
    (hp : AdmissibleAllocation E p)
    (hmax : ∀ p' : Outcome ι, AdmissibleAllocation E p' →
      virtualObjective E p' ≤ virtualObjective E p)
    (hx : ∀ t ∈ support E, ∀ i,
      x i t = p i t * bidderValue E i t -
        ∫ s in E.a i..t i, p i (Function.update t i s)) :
    IsOptimal E p x := by sorry

end MyersonAuction.Optimal
