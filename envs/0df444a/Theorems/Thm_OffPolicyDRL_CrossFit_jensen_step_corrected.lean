-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_jensen_step_corrected
-- name    : OffPolicyDRL.CrossFit.jensen_step_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:36.197597+00:00
-- url     : https://prove2.me/theorems/4e4ef84b-b392-4ba6-bcba-a4166ba77ae0
-- title:
--   Proof of Thm 6, Jensen step, corrected (factor C_η): ‖v̂(s′) − v(s′)‖₂ ≤ √(C_{S′}C_η)‖q̂ − q‖₂
-- statement:
--   Under the standing assumptions of the off-policy evaluation model, suppose:
--
--   1. the law of $s'$ under the behavior data is at most $C_{S'}$ times $p^{(0)}_{\pi_b}$, i.e. $p_{b,S'}/p_{b,S}\le C_{S'}$, with $C_{S'}>0$;
--   2. $\eta(s,a)\le C_\eta$ almost surely under $p^{(0)}_{\pi_b}\otimes\pi_b$, with $C_\eta>0$.
--
--   Let $\hat q:S\times A\to\mathbb R$ be bounded and measurable, and $\hat v(s)=\int\hat q(s,a)\,\pi_e(da\mid s)$. Then
--   $$\big\|\hat v(s')-v(s')\big\|_2\le\sqrt{C_{S'}C_\eta}\;\big\|\hat q(s,a)-q(s,a)\big\|_2 .$$
--   The left norm is under the law of $s'$ in the data; the right norm is under $p^{(0)}_{\pi_b}\otimes\pi_b$.
--
--   The paper states this with the factor $\sqrt{C_{S'}}$, which is false. Example: one state with $s'=s$, two actions, $\pi_b$ uniform, $\pi_e$ the point mass on action 1, $r\equiv0$, and $\hat q=\mathbf 1\{a=1\}$. Then the left side is $1$ and $\sqrt{C_{S'}}\|\hat q-q\|_2=1/\sqrt2$. The extra factor $C_\eta$ accounts for the change of measure from $\pi_e$ to $\pi_b$. **Corrected.**
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Appendix C, Proof of Theorems 6 and 7, "Term (28) is op(1)", p. 60 (corrected: factor C_η added)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem jensen_step_corrected {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (CS' Cη : ℝ) (hCS' : 0 < CS') (hCη : 0 < Cη)
    (hS' : M.obsLaw.map (fun o => o.2.2.2) ≤ ENNReal.ofReal CS' • M.ν0b)
    (hη : ∀ᵐ x ∂(M.ν0b ⊗ₘ M.πb), M.η x.1 x.2 ≤ Cη)
    (qh : S × A → ℝ) (hqh : Measurable qh) (hqhb : ∃ C : ℝ, ∀ x, |qh x| ≤ C) :
    √(∫ o, (M.vOf' qh o.2.2.2 - M.v o.2.2.2) ^ 2 ∂M.obsLaw) ≤
      √(CS' * Cη) * M.normSA (fun x => qh x - M.q x) := by sorry

end OffPolicyDRL.CrossFit
