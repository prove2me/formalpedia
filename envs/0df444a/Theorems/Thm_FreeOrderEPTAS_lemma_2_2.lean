-- Prove2me | Theorems.Thm_FreeOrderEPTAS_lemma_2_2
-- name    : FreeOrderEPTAS.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:06.067099+00:00
-- url     : https://prove2.me/theorems/1923aba9-5b00-488d-b64e-95d3f7c1ea82
-- title:
--   Lemma 2.2 — (LP) is feasible (corrected: capped small-load guess)
-- statement:
--   Let $x^{(\mathrm{IP})}$ be feasible for (IP), let $\delta\in(0,1)$ with $1/\delta$ an integer, $\epsilon>0$, $\xi\in[0,1/2]$, and let $N^\downarrow,N^\uparrow,S^\downarrow$ be the guesses induced by $x^{(\mathrm{IP})}$. Then the vector
--   $$\hat y_{(i,t),j}=\begin{cases}x^{(\mathrm{IP})}_{ij}&N^{(\mathrm{IP})}_{it}\le2/\delta\\(1-\xi)\,x^{(\mathrm{IP})}_{ij}&N^{(\mathrm{IP})}_{it}>2/\delta\end{cases}$$
--   is feasible for (LP).
--
--   So the enumeration of guesses reaches a feasible LP whenever (IP) is feasible.
--
--   Differences from the source:
--   - correction: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, p.10 → $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$; reason: the printed guess has order $n$ values ($n$ jobs of load $\delta$ in one class, all on machine $i$), a PTAS count against the stated $O((T/\epsilon)^{O(mDT)})$; every step of the proof survives the cap
--   - reading: (LP) "is feasible" under the running assumption, for the guesses of §2.3 → the guesses are hypotheses tied to $x^{(\mathrm{IP})}$, and the conclusion names the witness $\hat y$ of p.14; reason: the lemma has no meaning apart from the guesses; the witness is the one of the proof
--   - encoding: $\xi\in(0,1)$, set to $\epsilon/2$ with $\epsilon\in(0,1)$ → $\xi\in[0,1/2]$; reason: covers the value used; the proof uses $1-\xi\ge1/2$
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Lemma 2.2, p.11; ŷ, p.14

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess

namespace FreeOrderEPTAS

/-- Lemma 2.2, p.11 (arXiv:2007.13121v3), with the proof's witness, p.14: for a feasible `x^(IP)`
and the guesses it induces, `ŷ` is feasible for (LP). -/
theorem lemma_2_2 {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ) (hϵ : 0 < ϵ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hδint : ∃ N : ℕ, 1 / δ = (N : ℝ)) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 2)
    (x : Assignment m n) (hcard : MeetsCard I x) (hload : LoadAtLeast I x 1)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo) :
    (mkLP I ϵ δ ξ Nlo Nhi Slo).Feasible (yhat I ϵ δ ξ x) := by sorry

end FreeOrderEPTAS
