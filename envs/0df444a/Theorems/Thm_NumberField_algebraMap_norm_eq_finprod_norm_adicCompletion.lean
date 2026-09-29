-- Prove2me | Theorems.Thm_NumberField_algebraMap_norm_eq_finprod_norm_adicCompletion
-- name    : NumberField.algebraMap_norm_eq_finprod_norm_adicCompletion
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:22.09592+00:00
-- url     : https://prove2.me/theorems/ec7d9a49-7de2-4fb1-8fe8-ba6ce4190a0f
-- title:
--   Local–global norm formula $N_{K/F}(x)=\prod_{w\mid v}N_{K_w/F_v}(x)$
-- statement:
--   Let $K/F$ be a finite extension of number fields, let $v$ be a finite place of $F$, i.e. a nonzero prime ideal of $\mathcal O_F$, and let $F_v$ be the $v$-adic completion of $F$. For each prime $w$ of $\mathcal O_K$ lying over $v$ (written $w \mid v$), let $K_w$ be the $w$-adic completion of $K$, regarded as an $F_v$-algebra via the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$. Then for every $x \in K$, the image of the global norm in $F_v$ is the product of the local norms:
--
--   $$
--   N_{K/F}(x) \;=\; \prod_{w \mid v} N_{K_w/F_v}(x) \qquad \text{in } F_v .
--   $$
--
--   This identity connects global norms with local norms at a finite place; it is used for instance to show that the semilocal norm map on local units sends diagonally embedded global units to diagonally embedded global norms, and in the local–global analysis of norm groups.
--
--   **Formalization Note** Mathlib at this revision provides no canonical algebra structure $F_v \to K_w$. As in Mathlib's own `NumberField.HeightOneSpectrum` API (the instance `Module.Finite Kv Lw` in `NumberField/Completion/FinitePlace.lean`), the statement takes, for each $w$, an arbitrary $F_v$-algebra structure on $K_w$ that is continuous (`ContinuousSMul`) and compatible with $F \to K$ (`IsScalarTower F F_v K_w`). Since $F$ is dense in $F_v$, such a structure is unique, and it exists (the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$) exactly when $w \mid v$; so the hypotheses just name the canonical embedding. Primes $w \mid v$ are the height-one primes $w$ of $\mathcal O_K$ with `w.asIdeal.LiesOver v.asIdeal`; there are finitely many, and the finite sum/product is written with `finsum`/`finprod` so that no finiteness hypothesis is needed.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der math. Wiss. 322, Springer 1999, Chapter II, §8, Corollary (8.4): $N_{L|K}(\alpha)=\prod_{w\mid v}N_{L_w|K_v}(\alpha)$ (finite-place case).

import Mathlib

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField

theorem algebraMap_norm_eq_finprod_norm_adicCompletion {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F))
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Algebra (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      ContinuousSMul (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      IsScalarTower F (v.adicCompletion F) (w.1.adicCompletion K)]
    (x : K) :
    algebraMap F (v.adicCompletion F) (Algebra.norm F x) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion F) (algebraMap K (w.1.adicCompletion K) x) := by sorry

end NumberField
