-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_Supplement_lemma_9_2
-- name    : MultiplierAssoc206.Resolution.Supplement.lemma_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:34:36.440202+00:00
-- url     : https://prove2.me/theorems/ad1b4dca-a2ab-4f7a-81f2-b12cf92d1b6c
-- title:
--   Lemma 9.2 — Local consequences have constant-size Frege derivations
-- statement:
--   Fix a Frege system. For all natural numbers $k$ and $s$ there are numbers $D=D(k,s)$ and $S=S(k,s)$ with the following property. Let $\Gamma$ be a set of clauses whose variables form a set of at most $k$ variables, and let $G$ be a formula of size $|G|\le s$ (over any variables) such that $\Gamma$ implies $G$: every assignment satisfying all clauses of $\Gamma$ satisfies $G$. Then $G$ has a derivation $\pi$ from $\Gamma$ (each clause read as the disjunction of its literals) with
--   $$\operatorname{depth}(\pi)\le D,\qquad|\pi|\le S.$$
--   The numbers $D$ and $S$ depend only on the Frege system, $k$ and $s$, not on $\Gamma$, $G$ or the set of variables.
--
--   This is the Frege counterpart of the constant-size local derivations used in the resolution reduction; in the bounded-depth reduction it produces the constant-depth, constant-size derivations of each substituted clause from the clauses of $\mathrm{PM}(H)$ that imply it.
--
--   Differences from the source:
--   - reading: "a set Γ of clauses over k variables" → the clauses of Γ mention at most k distinct variables; reason: a set of clauses over k variables need not use all of them, and a bound for at most k variables is the same as a bound for exactly k, taking the maximum over k' ≤ k
--   - reading: "depend only on k and |G|" → D and S are chosen after the Frege system, k and a bound s on |G|, and before the variable type, Γ and G; reason: the bounds are uniform over all Γ and G with these parameters, and a bound for |G| ≤ s gives one for |G| = s
--   - reading: the size of a formula is "its number of symbols" → symbols counted in prefix form; reason: the source does not fix a notation
--   - encoding: implicational completeness for every Γ → required only for finite Γ in the definition of a Frege system; reason: equivalent by the compactness theorem, so the same systems qualify
--   - encoding: a clause as a formula → the disjunction of its literals listed in one fixed order; reason: the source does not specify an order
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.23 (printed p.22), Lemma 9.2 (Local consequences have constant-size Frege derivations)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Frege

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

/-- Lemma 9.2 (Local consequences have constant-size Frege derivations), PDF p.23 (printed
p.22): for a Frege system and all `k`, `s` there are `D`, `S` such that, whenever a set `Γ` of
clauses over at most `k` variables implies a formula `G` of size at most `s`, `G` has a
derivation from `Γ` of depth at most `D` and size at most `S`. -/
theorem lemma_9_2 (R : List Rule) (hR : IsFregeSystem R) (k s : ℕ) :
    ∃ D S : ℕ, ∀ (α : Type) (Γ : CNF α) (G : Formula α),
      (cnfVars Γ).card ≤ k → G.size ≤ s →
      (∀ a : α → Bool, CNFSat a Γ → G.eval a = true) →
        ∃ π : List (Formula α), IsDerivation R (cnfFormulas Γ) G π ∧
          derivDepth π ≤ D ∧ derivSize π ≤ S := by sorry

end MultiplierAssoc206.Resolution.Supplement
