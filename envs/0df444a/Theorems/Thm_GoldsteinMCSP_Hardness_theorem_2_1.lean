-- Prove2me | Theorems.Thm_GoldsteinMCSP_Hardness_theorem_2_1
-- name    : GoldsteinMCSP.Hardness.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:13:44.077115+00:00
-- url     : https://prove2.me/theorems/800ee6b8-b902-4739-8a71-c5da5f34fd72
-- title:
--   Theorem 2.1 — APX-hardness of both two-copy partition problems
-- statement:
--   Both unsigned and signed minimum common string partition with at most two copies of each underlying letter per input string are APX-hard:
--
--   $$\operatorname{APXHard}(2\text{-MCSP})\;\land\;\operatorname{APXHard}(2\text{-SMCSP}).$$
--
--   The inputs range over all related pairs of finite strings with arbitrary finite symbol support and length. In the signed problem relatedness counts underlying letters regardless of sign, and an allowed reversed block also has every sign flipped. Each objective is the minimum number of contiguous blocks matched by a permutation, including repeated blocks.
--
--   APX-hardness means membership in NPO together with a uniform polynomial-time PTAS-preserving reduction from every NPO optimization problem admitting a polynomial-time constant-factor approximation, including minimization and maximization problems. Accuracy transfer is positive, computable and independent of the instance. This assertion has no hypothesis of P≠NP, cubic-independent-set hardness, or a correct reduction.
--
--   Differences from the source:
--   - encoding: APX-hardness without an explicit machine model → NPO membership and hardness for all APX problems under uniform finite-alphabet bit-machine PTAS reductions; reason: makes the standard complexity semantics explicit; computational bounds concern actual machine steps
--   - encoding: finite unsigned and signed strings and partitions → canonical binary lists of natural labels, cut lengths, a block-index permutation and orientation bits; reason: represents every finite instance and feasible cut partition; rejects malformed encodings and preserves multiplicity
--   - encoding: partitions into contiguous blocks → cut partitions with nonempty blocks, and the empty partition of an empty word; reason: empty blocks may be deleted without changing the optimum; this makes the standard cut-partition convention explicit
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Theorem 2.1, printed p. 6 (PDF p. 6)

import Definitions.Def_GoldsteinMCSP_Hardness_Problems

namespace GoldsteinMCSP.Hardness

theorem theorem_2_1 :
    APXHard (partitionProblem false) ∧ APXHard (partitionProblem true) := by sorry

end GoldsteinMCSP.Hardness
