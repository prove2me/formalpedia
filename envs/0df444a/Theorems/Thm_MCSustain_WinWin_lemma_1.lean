-- Prove2me | Theorems.Thm_MCSustain_WinWin_lemma_1
-- name    : MCSustain.WinWin.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:24.981957+00:00
-- url     : https://prove2.me/theorems/577ec313-7b86-40f5-99ec-6a39ef90499c
-- title:
--   Lemma 1, p. 10 (PDF 10) — the MP firm stocks λm_H per variant if λ < λ_t and λm_L otherwise
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Fix a number of variants $n\ge0$ and a market share per variant $0\le\lambda\le1$ whose price covers the unit cost, $t\lambda\le2(r-c)$ (that is, $p_{MP}=r-\tfrac t2\lambda\ge c$). Let
--   $$q^*=\begin{cases}\lambda m_H,&\lambda<\lambda_t,\\ \lambda m_L,&\lambda\ge\lambda_t,\end{cases}\qquad \lambda_t=\frac{2(r-c/\alpha)}{t}.$$
--   Then for every stock level $q\ge0$,
--   $$\Pi(n,\lambda,q)\le\Pi(n,\lambda,q^*).$$
--
--   A small share per variant (a high price) makes it worth stocking for the high market size, which is the source of overproduction in the MP system.
--
--   **Formalization Note** The hypothesis $t\lambda\le2(r-c)$ is added: for larger $\lambda$ the price is below cost and stocking nothing is optimal, so the printed rule fails. Every solution type satisfies it. "Optimal" means a maximizer; at $\lambda=\lambda_t$ the profit is flat in $q$ on $[\lambda m_L,\lambda m_H]$.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. 10 (PDF 10), Lemma 1

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem lemma_1 (P : Params) (hP : P.Standing) (n lam : ℝ) (hn : 0 ≤ n) (hlam : 0 ≤ lam)
    (hlam_le : lam ≤ 1)
    (hprice : P.t * lam ≤ 2 * (P.r - P.c)) (q : ℝ) (hq : 0 ≤ q) :
    profitMP P ⟨n, lam, q⟩ ≤
      profitMP P ⟨n, lam, if lam < lamT P then lam * P.mH else lam * P.mL⟩ := by sorry

end MCSustain.WinWin
