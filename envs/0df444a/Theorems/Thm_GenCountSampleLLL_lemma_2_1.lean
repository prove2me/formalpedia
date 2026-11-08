-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_2_1
-- name    : GenCountSampleLLL.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:49:30.926928+00:00
-- url     : https://prove2.me/theorems/53bede6f-f118-43f2-bd42-0bfd529a4e15
-- title:
--   Lemma 2.1, p.7 — $Z_{\mathcal D}>0$, $r_{\mathcal D,a}\le cx_a$, and $1\le Z_{\mathcal E}/Z_{\mathcal D}\le\prod_{b\in\mathcal D\setminus\mathcal E}(1-cx_b)^{-1}$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$. Then:
--   1. $Z_{\mathcal D}>0$ for every $\mathcal D\subseteq\mathcal C$;
--   2. for every $a\in\mathcal D\subseteq\mathcal C$, $r_{\mathcal D,a}\le c\,x_a$;
--   3. for $\mathcal E\subseteq\mathcal D\subseteq\mathcal C$,
--   $$
--   1\le\frac{Z_{\mathcal E}}{Z_{\mathcal D}}\le\prod_{b\in\mathcal D\setminus\mathcal E}\frac1{1-c\,x_b}.\tag{2.1}
--   $$
--
--   The bounds control every conditional probability and every ratio of partition functions in the counting and sampling analyses.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - generalization: Lemma 2.1 asserts the two bounds; Z_𝒟 > 0 for every 𝒟 is asserted in the text of §2 just before it → the positivity of every Z_𝒟 is a further conjunct; reason: it is the paper's own claim ("ZD > 0 for every D ⊆ C"); dropping the conjunct gives the lemma
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 2.1 and the opening paragraph of §2, p.7

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Lemma 2.1, p.7 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), with the standing assumption of §2: (1.1) with
`c = 1/100`. Under (1.1), `Z_D > 0` for every `D ⊆ C` (§2, p.7); for every `a ∈ D ⊆ C`,
`r_{D,a} ≤ c x_a`; and for `E ⊆ D ⊆ C`, `1 ≤ Z_E/Z_D ≤ ∏_{b ∈ D∖E} 1/(1 − c x_b)` (2.1).

**Formalization Note.** `r_{D,a} = µ_{D⁻}(B_a)`; the positivity of every `Z_D`, asserted in the
text of §2, is stated as the first conjunct, so no division below is by zero. -/
theorem lemma_2_1 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) :
    (∀ D : Finset (Fin I.m), 0 < I.Z D) ∧
    (∀ (D : Finset (Fin I.m)) (a : Fin I.m), a ∈ D → I.r D a ≤ 1 / 100 * x a) ∧
    (∀ D E : Finset (Fin I.m), E ⊆ D →
      1 ≤ I.Z E / I.Z D ∧ I.Z E / I.Z D ≤ ∏ b ∈ D \ E, 1 / (1 - 1 / 100 * x b)) := by sorry

end GenCountSampleLLL
