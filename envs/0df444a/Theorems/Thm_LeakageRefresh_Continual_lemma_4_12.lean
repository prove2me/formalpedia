-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_12
-- name    : LeakageRefresh.Continual.lemma_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:31.629232+00:00
-- url     : https://prove2.me/theorems/21d60d30-9a62-4a4b-8640-995e2a3f572c
-- title:
--   Lemma 4.12 — four cycles after a refresh: $\mathbb E_M\mathrm{Cyc}(\Delta^M)\le64\,\mathrm{Cyc}(\Delta)+\frac{32B_2^2}{q}t^2+\frac{72B_\infty^2}{q^2}t^2$
-- statement:
--   Let $n\ge2$, $q=2^n-1$, and let $\Delta:U_L^2\times U_R^2\to\mathbb R$ be any real table supported on consistent tuples. Put $t=\|\Delta\|_2$ and $B_\infty=\|\Delta\|_\infty$, and let $B_2\ge0$ bound the $L^2$ norm of every row and every column of $\Delta$. Then
--   $$\mathbb E_{M\leftarrow\mathrm{InvMatr}^n_2}\big[\mathrm{Cyc}(\Delta^M)\big]\le64\,\mathrm{Cyc}(\Delta)+\frac{32B_2^2}{q}t^2+\frac{72B_\infty^2}{q^2}t^2, \tag{4.47}$$
--   where $\Delta^M(\ell,r)=\Delta((\ell,\ell M),(r,M^{-1}r))$ is a table on $U_L\times U_R$ and $\mathrm{Cyc}$ is the four-cycle average of Eq. (4.41).
--
--   Differences from the source:
--   - encoding: "supported on consistent tuples"; "$B_2$ bounds the L2 norm of every row and every column" → $\Delta=0$ at every inconsistent tuple; `l2 (Δ p) ≤ B₂` for each row $p$ and `l2 (fun p => Δ p q) ≤ B₂` for each column $q$; reason: the hypotheses written out with the probability-normalized row and column norms
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 38, Lemma 4.12

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.12 (Four cycles after a refresh).** Let `∆ : U_L² × U_R² → ℝ` be supported on
consistent tuples, `t = ‖∆‖₂`, `B_∞ = ‖∆‖_∞`, and `B₂ ≥ 0` bound the L2 norm of every row and
every column. With `q = 2ⁿ − 1`,
`E_{M ←$ InvMatr}[Cyc(∆^M)] ≤ 64 Cyc(∆) + (32 B₂²/q) t² + (72 B_∞²/q²) t²`. -/
theorem lemma_4_12 (n : ℕ) (hn : 2 ≤ n) (Δ : Table4 n)
    (hΔ : ∀ p q, ¬ consistent (p, q) → Δ p q = 0) (B₂ : ℝ) (hB₂ : 0 ≤ B₂)
    (hrow : ∀ p, l2 (Δ p) ≤ B₂) (hcol : ∀ q, l2 (fun p => Δ p q) ≤ B₂) :
    avg (fun M : InvMatr n => cyc (atMatrix Δ M)) ≤
      64 * cyc Δ + 32 * B₂ ^ 2 / ((2 : ℝ) ^ n - 1) * tableL2 Δ ^ 2 +
        72 * supNorm Δ ^ 2 / ((2 : ℝ) ^ n - 1) ^ 2 * tableL2 Δ ^ 2 := by sorry

end LeakageRefresh.Continual
