-- Prove2me | Theorems.Thm_LiftSAParity_theorem_4_1_lifting
-- name    : LiftSAParity.theorem_4_1_lifting
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:30.142909+00:00
-- url     : https://prove2.me/theorems/4f56fd08-42af-4331-a081-660c0d601301
-- title:
--   Theorem 4.1 — $d$-local distributions lift to SA(⊕) coefficient size $\exp(\Omega(d/\ell^3))$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $\ell\ge2$, let $g:\{0,1\}^\ell\to\{0,1\}$ be a 1-stifling gadget, and let $F$ be an unsatisfiable CNF formula on $n$ variables that admits a $d$-local distribution, where $d\ge4\ell$. Then
--
--   1. every semantic SA(⊕) refutation of $F\circ g$ has coefficient size at least $\exp(c\,d/\ell^3)$;
--   2. every SA(⊕) refutation of $F\circ g$ has coefficient size at least $\exp(c\,d/\ell^3)$.
--
--   This is the formal version of the main result: the measure $\mu$ built from the local distribution satisfies Lemma 3.4 with $r=\lfloor d/2\ell\rfloor$ and $\delta=e^{-d/8\ell^3}$. Clause 2 follows from clause 1, from the transfer `semantic_subsumes_syntactic` (a factor $3$), and from the elementary bound that every SA(⊕) refutation of a formula without the empty clause has coefficient size at least $2$: evaluating the identity at the all-zero point forces $\sum_I\|q_{c_I}\|\ge1$, and evaluating it at a Boolean point forces $\sum_C\|q_{p_C}\|\ge1$. This costs only a smaller $c$ ($c=1/32$ suffices).
--
--   **Formalization Note** $c$ is chosen before all other parameters.
--
--   Differences from the source:
--   - reading: coefficient size at least exp(Ω(d/ℓ³)) → one constant c > 0, uniform in n, ℓ, d, g and F, with bound exp(c·d/ℓ³); reason: the standard meaning of Ω with a single absolute constant
--   - generalization: any SA(⊕) refutation (p.13; "Our lower bounds actually hold for a stronger, semantic system", p.9) → clause (a) for semantic SA(⊕) refutations and clause (b) for SA(⊕) refutations, both with the same c; reason: clause (b) is the printed bound; clause (a) adds the semantic system of p.9, for which the paper's proof runs
--   - reading: F ∘ g (not defined in the paper) → the canonical CNF encoding `lift F g`; reason: each lifted clause excludes one falsifying assignment of the blocks of its source clause, the encoding the proof of item (3) uses
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the only unsatisfiable formula is {∅}, which has no local distribution, so the case is vacuous; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4, p.13, Theorem 4.1

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsOneStifling
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_SemSAXorRefutation
import Definitions.Def_LiftSAParity_SAXorRefutation

namespace LiftSAParity

/-- **Theorem 4.1** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4, p.13): "Given ℓ ≥ 2 and a 1-stifling gadget g : {0, 1}^ℓ → {0, 1}, if
F is an unsatisfiable CNF formula that admits a d-local distribution for d ≥ 4ℓ, then any SA(⊕)
refutation of φ = F ◦ g has coefficient size at least exp(Ω(d/ℓ³))."

There is one absolute constant `c > 0` such that, for all `n`, `ℓ ≥ 2`, `d ≥ 4ℓ`, every 1-stifling
`g` and every unsatisfiable `F` on `n` variables with a `d`-local distribution: (a) every semantic
SA(⊕) refutation of `F ∘ g` has coefficient size at least `exp(c·d/ℓ³)`, and (b) every SA(⊕)
refutation of `F ∘ g` has coefficient size at least `exp(c·d/ℓ³)`.

**Formalization Note** `exp(Ω(d/ℓ³))` is read as one `c > 0` uniform in every parameter. Clause (b)
is the printed bound; clause (a) is the semantic system for which the paper's proof runs (p.9). -/
theorem theorem_4_1_lifting : ∃ c : ℝ, 0 < c ∧
    ∀ (n ℓ d : ℕ) (g : (Fin ℓ → Bool) → Bool) (F : CNF (Fin n)),
      2 ≤ ℓ → IsOneStifling g → ¬ Satisfiable F →
      (∃ D : (I : Finset (Fin n)) → (I → Bool) → ℝ, IsLocalDist F d D) → 4 * ℓ ≤ d →
      (∀ π : SemSAXorRefutation (lift F g),
          Real.exp (c * (d : ℝ) / (ℓ : ℝ) ^ 3) ≤ π.coeffSize) ∧
      (∀ π : SAXorRefutation (lift F g),
          Real.exp (c * (d : ℝ) / (ℓ : ℝ) ^ 3) ≤ π.coeffSize) := by sorry

end LiftSAParity
