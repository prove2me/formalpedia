-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_network_congestion_cls_complete
-- name    : NetworkEquilibriumCLS.LinearNash.network_congestion_cls_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:38.60551+00:00
-- url     : https://prove2.me/theorems/790cd978-28e6-468e-b48b-02fd5bd10b35
-- title:
--   Theorem 5.1 — exact linear-network Nash is CLS-complete, with DAG hardness
-- statement:
--   An input gives an explicitly listed finite directed network, unweighted players with feasible source/destination pairs, and nonnegative rational coefficients α_e for the homogeneous latency ℓ_e(k)=α_e k. Every simple directed terminal path is an action. Players choose paths independently, and exact Nash means that no player can decrease expected cost by deviating to any feasible simple path.
--
--   The output lists, for each player, rational probabilities on simple paths, nonnegative and summing to one. There is one exponent, independent of all input data, bounding the total answer encoding. For this exact search problem,
--
--   $$\mathrm{Network\text{-}Congestion\text{-}Nash}\in\mathrm{CLS},$$
--   $$\mathrm{Network\text{-}Congestion\text{-}Nash}\text{ is CLS-hard already on unweighted directed acyclic networks}.$$
--
--   The statement also records membership for the restricted inputs and hardness for unrestricted inputs, so both classes are complete. Membership includes totality and polynomial verification, and hardness quantifies over every problem in the fixed canonical CLS class using genuine polynomial-time instance maps and decoders valid for every target answer. No support cap is imposed on actions or deviations. Zero latencies, irrelevant vertices and coincident terminals are included; the latter admit a trivial path. No reduction correctness or background classification is a hypothesis.
--
--   This is the full detailed form of Main Theorem 1, with unrestricted membership and the stronger acyclic hardness conclusion. The local proposal authors the statement and supporting interfaces; it does not supply proofs of the classification.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: polynomially encoded exact search answers → one exponent k chosen before all inputs, with total answer length at most (input length + 1)^k + k; reason: existence of k states the uniform polynomial output guarantee without inventing a numerical degree; totality and verification are conclusions inside CLS membership
--   - generalization: directed graph instances and DAG hardness → membership also permits distinct parallel edges; the DAG hardness target additionally has no parallel edges; reason: ordinary directed graphs embed directly; subdividing parallel edges gives the usual membership extension, and the source triangular construction already has no parallel edges, so the stronger hardness promise implies the full source claim under either graph convention
--   - encoding: simple terminal paths and independent path lotteries → finite edge-set actions witnessed by ordered simple directed paths; sparse answers retain edge-list paths; reason: a nontrivial directed simple path is determined by its edge set, and the empty path handles equal terminals; no feasible action or deviation is omitted
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.14 (PDF 15), Theorem 5.1; p.2 (PDF 3), Main Theorem 1 and §1.1 input/output specification; proof pp.14–16 (PDF 15–17).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem network_congestion_cls_complete :
    ∃ k : ℕ, InCLS (bounded networkSearch k) ∧
    InCLS (bounded dagSearch k) ∧ CLSHard (bounded dagSearch k) ∧
    CLSHard (bounded networkSearch k) := by sorry

end NetworkEquilibriumCLS.LinearNash
