-- Prove2me | Theorems.Thm_NearOptOWF_lemma_3_6
-- name    : NearOptOWF.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:36.60573+00:00
-- url     : https://prove2.me/theorems/0474041f-57c4-4a33-b46b-228f49935af1
-- title:
--   Lemma 3.6 — sub-exponentially secure puncturable PRFs from iO and $\mathsf{coNP}\not\subseteq_{\mathrm{i.o.}}\mathsf{NP}$
-- statement:
--   Assume $\mathsf{coNP} \not\subseteq_{\mathrm{i.o.}} \mathsf{NP}$ and that a sub-exponentially secure indistinguishability obfuscator exists. Then there exists a sub-exponentially secure puncturable PRF.
--
--   The lemma supplies the puncturable PRFs $F$, $G$, $H$ of the construction: in the proof of Theorem 4.1 its hypothesis follows from $\mathsf{NP} \not\subseteq_{\mathrm{i.o.}} \mathsf{coAM}$, since $\mathsf{NP} \subseteq \mathsf{AM}$.
--
--   Differences from the source:
--   - reading: coNP ⊄_{i.o.} NP ("a reduction that works on every instance at infinitely many input lengths") → some L with complement in NP agrees with no NP language on all inputs of length n for infinitely many n; reason: the standard reading of the infinitely-often inclusion
--   - reading: sub-exponentially secure indistinguishability obfuscator (Definition 3.4, "PPT (resp. polynomial-size) distinguisher", "poly(ε)" advantage) → multi-output circuits, perfect correctness for every coin string, security against non-uniform circuits of size ≤ p(λ) on functionally equivalent pairs of equal size with n ≤ p(λ), advantage ≤ 2^{-λ^δ} for some δ > 0; reason: the proof of Claim 4.7 (p.19) uses the non-uniform variant; equal size is the paper's padding (pp.11–12) and without it no iO exists; ∃δ absorbs poly(ε)
--   - reading: sub-exponentially secure puncturable PRF (never defined in the paper) → standard Sahai–Waters/[CCR16] definition with parameters (λ, n, m): polynomial-time key, puncturing and evaluation, punctured correctness, non-uniform selective security with advantage ≤ 2^{-λ^δ}; reason: the paper uses the primitive without a definition; this is the standard one with §3's sub-exponential security
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.6, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NearOptOWF_CoNPNotSubsetIoNP
import Definitions.Def_NearOptOWF_SubexpIOExists
import Definitions.Def_NearOptOWF_PPRF_IsSubexpPPRF

namespace NearOptOWF

/-- **Lemma 3.6** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 3.6, p.9 (PDF p.11)): assuming `coNP ⊄_{i.o.} NP` and the existence
of a sub-exponentially secure indistinguishability obfuscator, there exists a sub-exponentially secure
puncturable PRF. -/
theorem lemma_3_6 (hcoNP : CoNPNotSubsetIoNP) (hIO : SubexpIOExists) :
    ∃ F : PPRF, F.IsSubexpPPRF := by sorry

end NearOptOWF
