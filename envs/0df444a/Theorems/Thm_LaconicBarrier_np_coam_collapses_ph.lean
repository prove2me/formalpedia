-- Prove2me | Theorems.Thm_LaconicBarrier_np_coam_collapses_ph
-- name    : LaconicBarrier.np_coam_collapses_ph
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:02.462426+00:00
-- url     : https://prove2.me/theorems/94b1eb2d-9aa7-4a5f-8b3f-06de76b3c4be
-- title:
--   Corollary 1.2 and [BHZ87] — $\mathsf{NP} \subseteq \mathsf{coAM}$ collapses the polynomial hierarchy
-- statement:
--   If every NP language $L_{\mathcal R}$ lies in $\mathsf{coAM}$ (one round, polynomial verifier time, communication and randomness), then the polynomial hierarchy collapses: there is a $k$ such that
--   $$
--   \Sigma_j^{\mathsf P} \subseteq \Sigma_k^{\mathsf P} \quad \text{for every } j.
--   $$
--
--   This is the result of Boppana, Håstad and Zachos that the paper cites for its headline consequence; it turns $\mathsf{NP} \subseteq \mathsf{coAM}$ into a collapse.
--
--   Differences from the source:
--   - reading: 'the polynomial hierarchy collapses' → ∃ k, ∀ j, Σ_j^P ⊆ Σ_k^P (the published KarpLiptonOM.SigmaP); reason: the meaning of a collapse; [BHZ87] gives k = 2
--   - encoding: NP ⊆ coAM → every language L_R of an NP relation is InCoAMPoly; reason: NP is the class of languages of NP relations
--   - encoding: coAM(rounds = 1, verifier time, comm, randomness = poly(n)), default errors 1/3 → InCoAMPoly: a one-round public-coin proof of the complement with all bounds (|x|+2)^d for one d, completeness ≥ 2/3, soundness ≤ 1/3; reason: one exponent bounds all four polynomials (take the maximum)
--   - encoding: NP relation: polynomial-time decidable, witness bound q → IsNPRel: the published PolyPred2 (one-tape CookPvsNP machines on x#w) and |w| ≤ q(|x|) for a polynomial q; reason: same class of relations and languages
--   - encoding: algorithms in an unspecified machine model ('polynomial time', 'T-time', 'verifier time') → one uniform deterministic two-tape oracle machine (KarpLiptonOM.OracleTM, empty oracle) per algorithm, on tuple-encoded inputs, coins as an extra input; reason: the paper names no machine model; every bound in this statement is polynomially robust
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), abstract, PDF p.1; Corollary 1.2, p.4 (PDF p.7); [BHZ87], cited p.3

import Mathlib
import Definitions.Def_LaconicBarrier_Lang
import Definitions.Def_LaconicBarrier_InCoAMPoly
import Definitions.Def_KarpLiptonOM_SigmaP

namespace LaconicBarrier

/-- **`NP ⊆ coAM` collapses the polynomial hierarchy** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), abstract, PDF p.1; Corollary 1.2, p.4:
"imply `NP ⊆ coAM`, and hence a collapse of the polynomial hierarchy"; [BHZ87], cited p.3): if every
NP language is in `coAM` (one round, polynomial verifier time, communication and randomness), then
there is a `k` with `Σ_j^P ⊆ Σ_k^P` for every `j`. -/
theorem np_coam_collapses_ph
    (h : ∀ (Rel : List Bool → List Bool → Prop) (q : Polynomial ℕ), IsNPRel Rel q →
      InCoAMPoly (Lang Rel)) :
    ∃ k : ℕ, ∀ j : ℕ, KarpLiptonOM.SigmaP j ⊆ KarpLiptonOM.SigmaP k := by sorry

end LaconicBarrier
