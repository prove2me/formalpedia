-- Prove2me | Theorems.Thm_MCSustain_WinWin_lemma_2
-- name    : MCSustain.WinWin.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:53.99956+00:00
-- url     : https://prove2.me/theorems/f5365c35-2af0-41b1-9354-e9796a4070ba
-- title:
--   Lemma 2, p. 14 (PDF 14) — the hybrid firm covers the whole market with MC at price r − w
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Let $y=(n,\lambda,q,p_{MC},\lambda_{MC})$ be any feasible hybrid decision, and let $y'$ be the same decision with
--   $$p_{MC}=r-w,\qquad \lambda_{MC}=1-n\lambda .$$
--   Then $y'$ is feasible and $\Pi'(y)\le\Pi'(y')$: for any choice of the mass-produced line, it is optimal to fill all gaps with mass-customized products and to charge the highest price at which consumers still buy them.
--
--   The lemma reduces the hybrid problem to the choice of the mass-produced line.
--
--   **Formalization Note** The page also gives the MC production quantity $q^*_{MC}=\lambda_{MC}M$; MC is made to order, so the model takes its expected sales to be $\mu\lambda_{MC}$ and has no MC stocking decision.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 14 (PDF 14), Lemma 2

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem lemma_2 (P : Params) (hP : P.Standing) (y : HybDec) (hy : y.Feasible P) :
    ({ y with pMC := P.r - P.w, lamMC := 1 - y.n * y.lam } : HybDec).Feasible P ∧
      profitHyb P y ≤ profitHyb P { y with pMC := P.r - P.w, lamMC := 1 - y.n * y.lam } := by sorry

end MCSustain.WinWin
