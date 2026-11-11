-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_25
-- name    : JainCRERepetition.Cubic.lemma_2_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:26.821555+00:00
-- url     : https://prove2.me/theorems/4ea58c20-cc49-47a3-b177-e10b2630ae9a
-- title:
--   Lemma 2.25 — retained records and ordered allocation
-- statement:
--   Assume the displayed full divergences are finite. For classical records with target probabilities $p_s$ and comparison probabilities $q_s$, the record divergence cancels:
--
--   $$D(\rho^{SRK}\|\nu^{SRK})-D(\rho^{SK}\|\nu^{SK})=\sum_sp_s\bigl[D(\rho_s^{RK}\|\nu_s^{RK})-D(\rho_s^K\|\nu_s^K)\bigr].$$
--
--   For matching local question copies and classical remote references, the ordered restriction averages sum exactly to $D(\rho\|\nu)-D(\rho^K\|\nu^K)$. If the comparison comes from the product prior, every target-supported conditional restriction has a density-form conditional comparison for the one-coordinate prior. All conditional blocks retain their own normalizations. Both Alice's forward order and Bob's reversed order are included by interchanging the local and remote alphabets and choosing the reverse coordinate order.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - generalization: Alice's forward coordinate order and Bob's reverse order → every permutation of the coordinate order; reason: simultaneously relabeling the finite coordinate registers reduces every order to the stated forward order; the reverse order specializes to Bob
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 19–20, Lemma 2.25, Eqs. (18)–(20); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_allocation

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_25 :
    (∀ (S R K : Type) [Fintype S] [Fintype R] [Fintype K]
      [DecidableEq S] [DecidableEq R] [DecidableEq K]
      (p q : Law S) (ρ ν : S → Op (R × K)),
      (∀ s, IsState (ρ s)) → (∀ s, IsState (ν s)) →
      FiniteD (cq p.p ρ) (cq q.p ν) →
      d (cq p.p ρ) (cq q.p ν) -
        d (cq p.p (fun s => trL (ρ s))) (cq q.p (fun s => trL (ν s))) =
        ∑ s, p.p s * (d (ρ s) (ν s) - d (trL (ρ s)) (trL (ν s)))) ∧
    (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      [Nonempty X] [Nonempty Y] (μ : Law (X × Y)), AllocationClaim μ) := by sorry
end JainCRERepetition.Cubic
