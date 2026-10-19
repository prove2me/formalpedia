-- Prove2me | Theorems.Thm_MCSustain_WinWin_lemma_3
-- name    : MCSustain.WinWin.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:02.624997+00:00
-- url     : https://prove2.me/theorems/43c95dba-9159-403d-a990-817c5ee07a79
-- title:
--   Lemma 3, p. a2 (PDF 34) — the hybrid firm's MP stocking rule: λm_H if λ < λ_t, λm_L otherwise
-- statement:
--   Throughout, $P$ is a parameter point satisfying the paper's standing assumptions (written $\mathrm{Standing}(P)$; see the model definition): $0<\alpha<1$, $m_H>m_L>0$, $c/\alpha<r$, $c(\beta-1)(1-\alpha)/(\alpha\beta)<w<r-c$, with $\lambda_L=(r-c)/t<1$, together with $t,c,f>0$, nonnegative lifecycle impacts, $E_s>0$ and $E_l>0$.
--
--   Fix $n\ge0$, $0\le\lambda\le1$ with $t\lambda\le2(r-c)$, and arbitrary MC price $p_{MC}$ and share $\lambda_{MC}$. With $q^*=\lambda m_H$ if $\lambda<\lambda_t$ and $q^*=\lambda m_L$ otherwise, for every $q\ge0$,
--   $$\Pi'(n,\lambda,q,p_{MC},\lambda_{MC})\le\Pi'(n,\lambda,q^*,p_{MC},\lambda_{MC}).$$
--
--   This is the hybrid firm's version of Lemma 1, used in the proof of Proposition 2.
--
--   **Formalization Note** The hypothesis $t\lambda\le2(r-c)$ is added, as in Lemma 1.
-- source:
--   Alptekinoğlu & Örsdemir, Is Adopting Mass Customization a Path to Environmentally Sustainable Fashion?, accepted manuscript (MSOM, forthcoming; SSRN 3685235, Jan. 20, 2022), p. a2 (PDF 34), Lemma 3

import Mathlib
import Definitions.Def_MCSustain_WinWin_Model

namespace MCSustain.WinWin

theorem lemma_3 (P : Params) (hP : P.Standing) (n lam pMC lamMC : ℝ) (hn : 0 ≤ n)
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hprice : P.t * lam ≤ 2 * (P.r - P.c)) (q : ℝ) (hq : 0 ≤ q) :
    profitHyb P { n := n, lam := lam, q := q, pMC := pMC, lamMC := lamMC } ≤
      profitHyb P { n := n, lam := lam, q := if lam < lamT P then lam * P.mH else lam * P.mL,
                    pMC := pMC, lamMC := lamMC } := by sorry

end MCSustain.WinWin
