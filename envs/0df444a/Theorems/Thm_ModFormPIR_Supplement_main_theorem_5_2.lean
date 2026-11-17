-- Prove2me | Theorems.Thm_ModFormPIR_Supplement_main_theorem_5_2
-- name    : ModFormPIR.Supplement.main_theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:47:44.185773+00:00
-- url     : https://prove2.me/theorems/1159e3db-2286-4fbd-9a4a-916193220068
-- title:
--   Main Theorem 5.2 — two-server PIR with exponent $H_2(1/4)<0.8113$ and three-server PIR with exponent $\eta_{\mathrm{ends}}<0.7445$
-- statement:
--   Let $H_2$ be the binary entropy function and $\eta_{\mathrm{ends}}=0.7444\ldots$ the constant of Corollary 8.4. Then:
--
--   1. there is a two-server doubly-efficient PIR scheme with exponent $H_2(1/4)$, and $H_2(1/4)<0.8113$;
--   2. there is a three-server doubly-efficient PIR scheme with exponent $\eta_{\mathrm{ends}}$, and
--
--   $$0.7444\le\eta_{\mathrm{ends}}<0.7445 .$$
--
--   Here an $s$-server doubly-efficient PIR scheme with exponent $\rho$ (Definition 5.1) is an information-theoretically private $s$-server PIR scheme on $n$-bit databases in which each server stores $n+1$ bits computed in $n\cdot\mathrm{polylog}(n)$ time from public parameters sampled in expected $\mathrm{polylog}(n)$ time, the user uploads $O(\log^2n)$ bits to each server, and each server reads and sends back at most $n^{\rho+o(1)}$ bits, in time $n^{\rho+o(1)}$.
--
--   This is the Fourier-analytic track of the paper: the two-server scheme comes from Fig. 4 (Theorem 6.1) and the three-server one from the elementary "both ends" cone-delta functions on $\mathbb Z_3^d$ (Lemma 8.3). It gives the abstract's two-server figure $n^{0.82}$.
--
--   **Formalization Note** The scheme notion is the base mission's `HasScheme`; $H_2$ is `WildeQIT.binaryEntropy`; $\eta_{\mathrm{ends}}$ is `etaEnds`.
--
--   Differences from the source:
--   - reading: an s-server doubly-efficient PIR scheme with exponent ρ (Definition 5.1) → the base mission's `ModFormPIR.HasScheme s ρ` (Definition 5.1: one finite program triple on the base word RAM with bit probes, n + 1 stored bits, O(log² n) upload, n·polylog preprocessing, expected polylog parameter sampling, and (n+1)^{ρ+g(n)} reads, steps and answer bits with one g → 0); reason: the published goal Main Theorem 5.5 uses the same notion; Main Theorem 5.2 is the same kind of statement
--   - reading: η_ends = 0.7444 … → 0.7444 ≤ etaEnds; reason: a decimal expansion beginning 0.7444 together with the stated η_ends < 0.7445 means 0.7444 ≤ η_ends < 0.7445
--   - encoding: α* = the point where the two terms of η(α) are equal → alphaStar = sup of the points of [0, 1/3] where the first term is ≤ the second; reason: the difference of the two terms is continuous and strictly increasing on [0, 1/3], so the supremum is the unique crossing point
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Main Theorem 5.2, p.21 (PDF p.25); Corollary 8.4, p.31 (PDF p.35); proof in Appendix A, p.88 (PDF p.92)

import Mathlib
import Definitions.Def_ModFormPIR_Scheme
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_ModFormPIR_Supplement_Track1Exponent

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-- **Main Theorem 5.2** (Track 1: Fourier analysis), p.21 (PDF p.25). Henzinger, Ragavan, *Doubly-Efficient
Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
There is a two-server doubly-efficient PIR scheme with exponent `H₂(1/4) < 0.8113`, and a three-server one with
exponent `η_ends < 0.7445`, where `η_ends = 0.7444…` is the constant of Corollary 8.4.

**Formalization Note.** "An `s`-server doubly-efficient PIR scheme with exponent `ρ`" is the base mission's
`ModFormPIR.HasScheme s ρ` (Definition 5.1). `H₂` is the base-2 binary entropy `WildeQIT.binaryEntropy`;
`η_ends = η(α*)` is `etaEnds`, with `α*` the crossing point of Corollary 8.4. The exponents are the constants
themselves; the decimal bounds are separate clauses, and `η_ends = 0.7444…` is read as
`0.7444 ≤ η_ends`. -/
theorem main_theorem_5_2 :
    HasScheme 2 (WildeQIT.binaryEntropy (1 / 4)) ∧ WildeQIT.binaryEntropy (1 / 4) < 0.8113 ∧
    HasScheme 3 etaEnds ∧ 0.7444 ≤ etaEnds ∧ etaEnds < 0.7445 := by sorry

end Supplement

end ModFormPIR
