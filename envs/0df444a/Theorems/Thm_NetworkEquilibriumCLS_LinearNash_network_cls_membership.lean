-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_network_cls_membership
-- name    : NetworkEquilibriumCLS.LinearNash.network_cls_membership
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:59.739845+00:00
-- url     : https://prove2.me/theorems/22606a27-64ca-441c-8e6f-b170adc6175e
-- title:
--   Background — unrestricted exact linear-network Nash belongs to CLS
-- statement:
--   Let the input be any finite directed network with positive numbers of vertices and unweighted players, feasible terminal pairs, and homogeneous latencies ℓ_e(k)=α_e k for nonnegative rational α_e. All simple paths are available, and players randomize independently. With an exact rational equilibrium represented by a uniformly polynomial-size list of paths and probabilities for every player,
--
--   $$\mathrm{Network\text{-}Congestion\text{-}Nash}\in\mathrm{CLS}.$$
--
--   The uniform output exponent exists as part of the conclusion. There is no DAG, positive-latency or distinct-terminal promise. This supporting item records the known membership explicitly invoked in Theorem 5.1; no classification is assumed by the headline theorem.
--
--   Differences from the source:
--   - encoding: polynomial-time maps on explicitly supplied rational input → self-delimiting binary codes and the published Cook Turing-machine runtime, with a tagged input/answer pair for decoding; reason: one uniform machine and exponent are chosen before all instances; these codes are polynomially interconvertible with explicit binary lists
--   - encoding: polynomially encoded exact search answers → one exponent k chosen before all inputs, with total answer length at most (input length + 1)^k + k; reason: existence of k states the uniform polynomial output guarantee without inventing a numerical degree; totality and verification are conclusions inside CLS membership
--   - generalization: directed graph input → distinct parallel edges are permitted in the network carrier; reason: ordinary directed graphs embed directly, and subdividing each parallel edge preserves all simple path choices and homogeneous costs with polynomial overhead
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.14 (PDF 15), membership paragraph immediately following Theorem 5.1; Daskalakis–Papadimitriou, Continuous Local Search, SODA 2011, §3, Theorem 3.1, implicit-congestion clause; Filos-Ratsikas et al., PPAD-membership for Problems with Exact Rational Solutions, STOC 2024, §4.3.1, Theorem 4.4 (general PL concave games), combined with the source membership assertion. The 2024 §5 splittable-game theorem is not identified with this atomic game.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

namespace NetworkEquilibriumCLS.LinearNash

/-- Supporting background result explicitly invoked by the source proof. -/
theorem network_cls_membership : ∃ k : ℕ, InCLS (bounded networkSearch k) := by sorry

end NetworkEquilibriumCLS.LinearNash
