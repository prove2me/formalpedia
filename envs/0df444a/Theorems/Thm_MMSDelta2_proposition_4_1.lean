-- Prove2me | Theorems.Thm_MMSDelta2_proposition_4_1
-- name    : MMSDelta2.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:17.885775+00:00
-- url     : https://prove2.me/theorems/1529b992-4d6f-4f12-b5e1-1c189c79ed7f
-- title:
--   Proposition 4.1 — MMS existence for circuit valuations is in $\Delta_2^P$
-- statement:
--   Consider instances in which every agent's valuation is given by circuits that, on the characteristic vector of a bundle, output the bundle's value as a signed integer in binary. Deciding whether such an instance admits an MMS allocation is in $\Delta_2^P$:
--
--   $$\mathrm{CircuitMMS}\in\Delta_2^P.$$
--
--   This is the membership half of the completeness results; explicit rational additive valuations reduce to it after clearing denominators.
--
--   **Formalization Note** The value is sign-magnitude: a sign circuit and one circuit per magnitude bit (`CircuitVal`).
--
--   Differences from the source:
--   - reading: circuits that output the value as a signed integer in binary → a sign circuit and b single-output magnitude circuits; value (−1)^{sign}·Σ_k bit_k·2^k; reason: sign-magnitude with one circuit per output bit is polynomially interconvertible with a multi-output circuit and with two's complement
--   - generalization: valuations normalized, σᵢ(∅) = 0 (standing assumption, p.11) → circuit valuations with arbitrary v(∅), possibly negative or non-monotone; reason: the normalized instances form a subset recognizable in polynomial time (one circuit evaluation), and Δ₂ᴾ is closed under intersection with P, so the statement specializes to the normalized one
--   - encoding: Δ₂ᴾ = P^NP and many-one reductions in a 'standard' unspecified machine model → Δ₂ᴾ = ⋃_{A ∈ NP} P^A with Cook one-tape machines (CookPvsNP.NP, PolyReducible) and the KarpLiptonOM oracle machine (InP); reason: the paper fixes no machine model; these are standard polynomially equivalent models, and a polynomial-time oracle machine makes polynomially many adaptive queries
--   - encoding: explicit representation of circuits → codes circuitInstCode (n, m, gate counts, published circuitCode); n ≥ 1; non-codes are not in the language; reason: the paper fixes no encoding; this code is injective and polynomial-time decodable; n ≥ 1 excludes only the instance without agents
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Proposition 4.1 (†), p.11 (PDF p.13); proof pp.56–57 (PDF pp.58–59)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_CircuitMMSLang

namespace MMSDelta2

/-- **Proposition 4.1 (†)**, p.11 (PDF p.13); proof pp.56–57 (PDF pp.58–59).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

For valuations represented by circuits that, given the characteristic vector of a bundle, output
its value as a signed integer in binary, deciding whether an MMS allocation exists is in `Δ₂ᴾ`.

**Formalization Note.** A circuit valuation is a sign circuit and `b` magnitude-bit circuits
(sign-magnitude binary, `CircuitVal`); values may be negative and need not be normalized. The
language `CircuitMMSLang` contains the codes of instances with `n ≥ 1` agents that admit an MMS
allocation; `Δ₂ᴾ = P^NP` on the published Cook and oracle machines. -/
theorem proposition_4_1 : CircuitMMSLang ∈ Delta2P := by sorry

end MMSDelta2
