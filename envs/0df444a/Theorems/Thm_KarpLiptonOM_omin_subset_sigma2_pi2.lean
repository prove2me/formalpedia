-- Prove2me | Theorems.Thm_KarpLiptonOM_omin_subset_sigma2_pi2
-- name    : KarpLiptonOM.omin_subset_sigma2_pi2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:42.715391+00:00
-- url     : https://prove2.me/theorems/a56bfa00-70ad-466f-9a1c-d61f5858d2d3
-- title:
--   §A.2.3 — $\mathrm{OMIN}\subseteq\Sigma^{\mathrm P}_2\cap\Pi^{\mathrm P}_2$
-- statement:
--   Every language in OMIN is in the second level of the polynomial hierarchy, on both sides:
--   $$
--   \mathrm{OMIN} \subseteq \Sigma^{\mathrm P}_2 \cap \Pi^{\mathrm P}_2 .
--   $$
--   For $x \in \{0,1\}^n$, $x \in L$ iff some $m$ is $<_n$-minimal (no $m'$ with $m' <_n m$) and $D(x, m) = 1$, and similarly for $x \notin L$.
--
--   In particular OMIN, and every class below it, lies in PH.
--
--   Differences from the source:
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3, p.23 (unnumbered: "In particular, OMIN ⊆ Σ₂^P ∩ Π₂^P")

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OMIN
import Definitions.Def_KarpLiptonOM_SigmaP
import Definitions.Def_KarpLiptonOM_PiP

namespace KarpLiptonOM

/-- §A.2.3, p.23 (unnumbered claim): `OMIN ⊆ Σ₂^P ∩ Π₂^P`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem omin_subset_sigma2_pi2 : OMIN ⊆ SigmaP 2 ∩ PiP 2 := by sorry

end KarpLiptonOM
