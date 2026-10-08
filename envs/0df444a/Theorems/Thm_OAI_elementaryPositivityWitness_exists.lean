-- Prove2me | Theorems.Thm_OAI_elementaryPositivityWitness_exists
-- name    : OAI.elementaryPositivityWitness_exists
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.789118+00:00
-- url     : https://prove2.me/theorems/8538ae2d-f1eb-40bc-b46b-fe2043d67d52
-- statement:
--   The theorem states that for every natural number n and every natural unit interval graph G on n vertices, the type of permutation witnesses for G is nonempty. Here G consists of a function h on {0,…,n−1} that is monotone and satisfies i ≤ h(i) for all i; its edges join i<j exactly when j ≤ h(i). A permutation σ of the vertices is a nondescent if, whenever consecutive positions i and i+1 have σ(i+1) < σ(i), the values σ(i) and σ(i+1) are adjacent in G. A proper coloring with r colors is a map f into {0,…,r−1} giving different colors to adjacent vertices, and its ascent count is the number of edges i<j with f(i) < f(j). The chromatic polynomial of G in r variables is the sum over proper r-colorings f of the coefficient polynomial X raised to the ascent count of f (with coefficients in ℕ[X]), times the product of the variables x_{f(i)} over all vertices i. A permutation witness consists of an assignment of an integer partition of n to every nondescent permutation σ, such that for every r the chromatic polynomial equals the sum over nondescents σ of X^{inv_G(σ)} times the elementary symmetric polynomial indexed by the assigned partition in r variables, where inv_G(σ) counts pairs of positions a<b with σ(b) < σ(a) and σ(a), σ(b) adjacent in G. The theorem asserts such a witness exists.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ElementaryPositivity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ElementaryPositivity.lean; bytes 2024..2164
-- Kind: theorem; definition proof obligation extracted; recipe elementary_positivity_witness recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ElementaryPositivity

namespace OAI

theorem elementaryPositivityWitness_exists (n : ℕ)
    (G : ElementaryPositivity.NaturalUnitIntervalGraph n) :
    Nonempty G.PermutationWitness := by
  sorry

end OAI
