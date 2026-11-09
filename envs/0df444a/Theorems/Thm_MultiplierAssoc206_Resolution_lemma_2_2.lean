-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_2_2
-- name    : MultiplierAssoc206.Resolution.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:29.504673+00:00
-- url     : https://prove2.me/theorems/2d2be423-36c1-44a1-ab04-8830d9a05d24
-- title:
--   Substitution lemma
-- statement:
--   Let $\sigma$ be a substitution from the variables of a CNF $\Phi$ to constants and literals over another set of variables. If $\Phi$ has a resolution refutation $\pi$ of size $s$, then the CNF $\Phi\sigma$ — obtained by applying $\sigma$ to every clause, deleting false literals and omitting the clauses that have become trivially true — has a resolution refutation of size at most $s$.
--
--   The lemma is applied twice in the reduction: to the restriction $\rho$ and to the substitution of extension variables for the wires.
--
--   Differences from the source:
--   - reading: Φσ omits the clauses that have become trivially true → a clause is omitted when a literal becomes the constant true or when its image contains complementary literals; reason: the stronger of the two readings: omitting tautologies as well leaves fewer initial clauses; the lemma holds for it, and it implies the lemma for the reading that keeps tautologies
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.5 (printed p.4), Lemma 2.2

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

namespace MultiplierAssoc206.Resolution

/-- Lemma 2.2 (Substitution lemma), PDF p.5 (printed p.4). -/
theorem lemma_2_2 {α β : Type} (σ : Substitution α β) (Φ : CNF α) (π : List (Clause α))
    (hπ : IsRefutation Φ π) :
    ∃ π' : List (Clause β), IsRefutation (Φ.subst σ) π' ∧ π'.length ≤ π.length := by sorry

end MultiplierAssoc206.Resolution
