-- Prove2me | Theorems.Thm_FreeOrderEPTAS_lemma_2_3
-- name    : FreeOrderEPTAS.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:13.304224+00:00
-- url     : https://prove2.me/theorems/84298c07-bd6f-4938-8ac0-15cb45f40b87
-- title:
--   Lemma 2.3 — (IV) violated by at most $2\epsilon$ (corrected: capped small-load guess)
-- statement:
--   Let $\epsilon\in(0,1)$, $\xi=\epsilon/2$, $\delta\in(0,1)$ with (9), let $x^{(\mathrm{IP})}$ satisfy (IV), with its induced guesses, $y$ feasible for (LP), and a rounding with (P1)–(P3). Then
--   $$\mathbb P\Big(\sum_{j\in[n]}\ell_{ijd}X_{ij}\ge1-2\epsilon\ \ \forall i\in[m],\,d\in A_i\Big)\ge\frac12.$$
--
--   With the capped guess the proof uses $\sum_t\min\{S_t,1\}\ge\min\{\sum_tS_t,1\}$ in (5).
--
--   Differences from the source:
--   - correction: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, p.10 → $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$; reason: the printed guess has order $n$ values ($n$ jobs of load $\delta$ in one class, all on machine $i$), a PTAS count against the stated $O((T/\epsilon)^{O(mDT)})$; every step of the proof survives the cap
--   - generalization: the $\delta$ of p.12, $x^{(\mathrm{IP})}$ feasible → any $\delta\in(0,1)$ with (9) when $mDT\ge1$, and $x^{(\mathrm{IP})}$ satisfying (IV) only; reason: the proof uses (9) and (IV) of $x^{(\mathrm{IP})}$ only; when $mDT=0$ there is no active pair, or no job and then (IV) forces no active pair
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Lemma 2.3, p.13; (5), p.14

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace FreeOrderEPTAS

/-- Lemma 2.3, p.13 (arXiv:2007.13121v3): `P(X violates (IV) by at most 2ϵ) ≥ 1/2`, for `x^(IP)`
feasible, the guesses it induces, `y` feasible for (LP), `ξ = ϵ/2`, and `δ` with (9). -/
theorem lemma_2_3 {m D n : ℕ} (I : SCInstance m D n) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h9 : 0 < m * D * numTypes I ϵ δ → δ ≤ ϵ ^ 3 / (16 * (numTypes I ϵ δ : ℝ) *
      Real.log (2 * (m : ℝ) * (D : ℝ) * (numTypes I ϵ δ : ℝ))))
    (x : Assignment m n) (hload : LoadAtLeast I x 1)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ (ϵ / 2) x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo).Feasible y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd) :
    (1 / 2 : ℝ) ≤ pr (rnd (mkLP I ϵ δ (ϵ / 2) Nlo Nhi Slo) y)
      {Y | LoadAtLeast I Y (1 - 2 * ϵ)} := by sorry

end FreeOrderEPTAS
