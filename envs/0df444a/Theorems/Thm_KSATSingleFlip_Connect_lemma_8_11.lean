-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_8_11
-- name    : KSATSingleFlip.Connect.lemma_8_11
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:45:47.041778+00:00
-- url     : https://prove2.me/theorems/51c4b4e8-87a5-4f43-85ba-d3370bc7b18b
-- title:
--   Lemma 8.11 — Exponential-rate bound
-- statement:
--   For the binary entropy $H(b)=-b\ln b-(1-b)\ln(1-b)$ with $0\ln0=0$, define $$\Psi_\beta(a,b)=a(1-\ln a)+H(b)-\frac\beta2(a+b)^2+a\ln(e^{a+b}-1)+(a+b)[\ln\beta+(\beta^{-1}-1)\ln(1-\beta)].$$ Then $$\max_{0\le b\le1}\Psi_{13/34}(6/7,b)<-\frac{99}{2000000}.$$ This numerical bound makes the exponential rate in the witness count strictly negative. The formal statement uses the equivalent strict bound at every point of $[0,1]$; continuity on this compact interval ensures that the maximum is attained.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 8.11, printed p. 71 (PDF p. 73) of STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_WitnessRate

namespace KSATSingleFlip.Connect

/-- Lemma 8.11: the witness exponential rate is uniformly negative. -/
theorem lemma_8_11 :
    ∀ b ∈ Set.Icc (0 : ℝ) 1, witnessRate (13 / 34) (6 / 7) b < -(99 : ℝ) / 2000000 := by
  sorry

end KSATSingleFlip.Connect
