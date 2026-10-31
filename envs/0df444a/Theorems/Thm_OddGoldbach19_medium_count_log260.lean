-- Prove2me | Theorems.Thm_OddGoldbach19_medium_count_log260
-- name    : OddGoldbach19.medium_count_log260
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:52:40.002037+00:00
-- url     : https://prove2.me/theorems/72dc6a27-5992-4d42-8441-555fb65bebea
-- title:
--   A prime-sum count throughout the intermediate logarithmic range
-- statement:
--   Let $R(n)$ count the integers at most$n$ that are sums of two odd primes. For every $n\in\mathbb N$ with $26\le\log n\le260$,
--   $$R(n)\ge\frac{100}{1799}n.$$
--   This is the intermediate-range estimate used in the density-$1/9$ prime-sum argument. The portion above$\log n=100$ uses an independently checked8000-prime finite-shift certificate.
-- source:
--   Riesel and Vaughan, On sums of primes (1983), finite-shift second moment method, with explicit accepted pair estimates and kernel-checked finite data. The thresholds and auxiliary constants are those of this formal proof, rather than a claim of verbatim source-lemma constants.

import Mathlib
import Definitions.Def_Schnir_defs

theorem OddGoldbach19.medium_count_log260 (n : ℕ)
    (hlo : 26≤Real.log (n:ℝ)) (hhi : Real.log (n:ℝ)≤260) :
    (n:ℝ)*(100/1799:ℝ)≤(((Finset.range (n+1)).filter (fun s=>0<Schnir.r s)).card:ℝ) := by sorry
