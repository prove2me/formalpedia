-- Prove2me | Theorems.Thm_Nock_NPR_collision_table_prob_le
-- name    : Nock.NPR.collision_table_prob_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:09.912904+00:00
-- url     : https://prove2.me/theorems/e93713ca-de16-4da6-aa81-7686f2f2b53b
-- title:
--   NPR: collision table prob le
-- statement:
--   **corr:ion_single_security (main.tex:1197), probability form — union bound.**  With
--       `ε := ε_col = 2(2Λ−1)/|K|`, the probability that some pair among `k = |s|` nouns collides
--       is `≤ ε · k(k−1)/2`.  This is the paper's second (union-bound) inequality, main.tex:1200.
--
--       ⚠ **The paper's FIRST (tight) inequality `Pr ≤ 1 − (1−ε)^{k(k−1)/2}` is NOT proven here,
--       and is not soundly provable in this model.**  The paper's proof (main.tex:2361) obtains it
--       by asserting "the probability of no table collisions is `(1−p)^{k(k−1)/2}`", i.e. by
--       treating the `k(k−1)/2` pairwise collision events as *independent*.  In our (and the
--       paper's real) probability model those events all share the SAME random `r ∈ K`, so they
--       are NOT independent, and a product/independence bound is unavailable: the only estimate the
--       root-counting machinery yields is the ADDITIVE union bound (`card_biUnion_le`), giving the
--       `≤ ε·k(k−1)/2` below.  The product form is moreover genuinely FALSE in the worst case
--       admitted by our per-pair root-count bounds: for `m := k(k−1)/2` pairwise collision sets
--       that are pairwise disjoint (each of the maximal `2Λ−1` roots) and together partition `K`,
--       the collision probability is `1`, which exceeds `1−(1−ε)^m < 1`.  Consistently, our proven
--       union bound `ε·m` is `≥` the tight `1−(1−ε)^m` (Bernoulli, `one_sub_one_sub_pow_le`; equality
--       only in the degenerate `ε = 0` / `m ≤ 1` cases, strict for `m ≥ 2, ε > 0`), so the tight
--       expression is a stronger claim that this model cannot license.  The union bound below is the
--       rigorous, model-faithful claim; the paper describes a "non-optimal but easier to show" bound
--       (main.tex:2361) which is what we prove here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L641-L666
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L641-L666

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem Nock.NPR.collision_table_prob_le {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
          * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) := by sorry
