-- Prove2me | Theorems.Thm_LiftSAParity_theorem_1_1_lifting
-- name    : LiftSAParity.theorem_1_1_lifting
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:01.179668+00:00
-- url     : https://prove2.me/theorems/502fbe8c-265a-4f6d-b09d-0de066908b16
-- title:
--   Theorem 1.1 — Sherali–Adams degree $d$ lifts to uSA(⊕) size $2^{\Omega(d/\ell^3)}$ through any 1-stifling gadget
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $\ell\ge1$, let $g:\{0,1\}^\ell\to\{0,1\}$ be a 1-stifling gadget, let $\varphi$ be a CNF formula on $n$ variables, and let $d\ge4\ell$. Suppose $\varphi$ has no Sherali–Adams refutation of degree at most $d$. Then
--
--   1. every semantic SA(⊕) refutation of the lifted formula $\varphi\circ g$ has coefficient size at least $\exp(c\,d/\ell^3)$;
--   2. every SA(⊕) refutation of $\varphi\circ g$ has coefficient size at least $\exp(c\,d/\ell^3)$.
--
--   Thus every uSA(⊕) refutation of $\varphi\circ g$ has size $2^{\Omega(d/\ell^3)}$. Clause 2 follows from clause 1, from the transfer `semantic_subsumes_syntactic` (a factor $3$), and from the elementary bound that every SA(⊕) refutation of a formula without the empty clause has coefficient size at least $2$ (evaluate the identity at the all-zero point and at a Boolean point); this costs only a smaller $c$ ($c=1/32$ suffices). Since uSA(⊕) p-simulates reversible resolution over parities, this yields depth-unrestricted RevRes(⊕) lower bounds, for example for Tseitin formulas on expanders lifted with $\mathrm{MAJ}_3$.
--
--   **Formalization Note** uSA(⊕) is SA(⊕) with size the sum of the absolute values of the coefficients (p.4). The hypothesis is about plain Sherali–Adams over the $n$ variables of $\varphi$; the conclusion is about SA(⊕) over the $n\ell$ variables of $\varphi\circ g$. No unsatisfiability hypothesis is needed: a satisfiable $\varphi\circ g$ has no refutations.
--
--   Differences from the source:
--   - reading: size 2^{Ω(d/ℓ³)} → one constant c > 0, uniform in n, ℓ, d, g and φ, with bound exp(c·d/ℓ³); reason: the standard meaning of Ω with a single absolute constant; base e and base 2 differ by a constant factor in c
--   - generalization: every uSA(⊕) refutation, i.e. SA(⊕) with coefficient size (p.4; "Our lower bounds actually hold for a stronger, semantic system", p.9) → clause (a) for semantic SA(⊕) refutations and clause (b) for SA(⊕) refutations, both with the same c; reason: clause (b) is the printed bound; clause (a) adds the semantic system of p.9, for which the paper's proof runs
--   - reading: the lifted formula φ ∘ g (not defined in the paper) → the canonical CNF encoding `lift φ g`; reason: each lifted clause excludes one falsifying assignment of the blocks of its source clause
--   - reading: degree of a Sherali–Adams refutation (p.4 and footnote 1) → deg p + deg q_p ≤ d for every used axiom and deg h_α ≤ d; reason: the footnote's total degree of each term, before cancellation between terms; it gives the weakest hypothesis and hence the strongest theorem
--   - encoding: no lower bound on ℓ → 1 ≤ ℓ; reason: d/ℓ³ must be defined; a 1-stifling gadget has ℓ ≥ 2 anyway, so no instance is lost
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the only formulas are ∅ (satisfiable, so no refutation) and {∅} (refutable in degree 0), so the case is vacuous; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4, Theorem 1.1

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsOneStifling
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_SARefutation
import Definitions.Def_LiftSAParity_HasSADegreeAtMost
import Definitions.Def_LiftSAParity_SemSAXorRefutation
import Definitions.Def_LiftSAParity_SAXorRefutation

namespace LiftSAParity

/-- **Theorem 1.1** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §1.1, p.4): "Let g: {0, 1}^ℓ → {0, 1} be a 1-stifling gadget, and suppose
that φ has no Sherali–Adams refutation of degree at most d, where d ≥ 4ℓ. Then every uSA(⊕)
refutation of the lifted formula φ ◦ g has size 2^{Ω(d/ℓ³)}."

There is one absolute constant `c > 0` such that, for all `n`, `ℓ ≥ 1`, `d ≥ 4ℓ`, every 1-stifling
`g` and every CNF `φ` on `n` variables with no Sherali–Adams refutation of degree at most `d`:
(a) every semantic SA(⊕) refutation of `φ ∘ g` has coefficient size at least `exp(c·d/ℓ³)`, and
(b) every SA(⊕) refutation of `φ ∘ g` has coefficient size at least `exp(c·d/ℓ³)`.

**Formalization Note** uSA(⊕) is SA(⊕) with size the coefficient size (p.4); both the syntactic
system and the semantic one (§3, p.9) are covered. `2^{Ω(d/ℓ³)}` is read as one `c > 0` uniform in
every parameter (base `e` and base `2` differ by a constant in `c`). `ℓ ≥ 1` makes `d/ℓ³` defined;
a 1-stifling gadget has `ℓ ≥ 2` anyway. -/
theorem theorem_1_1_lifting : ∃ c : ℝ, 0 < c ∧
    ∀ (n ℓ d : ℕ) (g : (Fin ℓ → Bool) → Bool) (φ : CNF (Fin n)),
      1 ≤ ℓ → IsOneStifling g → 4 * ℓ ≤ d →
      (¬ ∃ π : SARefutation φ, HasSADegreeAtMost π d) →
      (∀ π : SemSAXorRefutation (lift φ g),
          Real.exp (c * (d : ℝ) / (ℓ : ℝ) ^ 3) ≤ π.coeffSize) ∧
      (∀ π : SAXorRefutation (lift φ g),
          Real.exp (c * (d : ℝ) / (ℓ : ℝ) ^ 3) ≤ π.coeffSize) := by sorry

end LiftSAParity
