-- Prove2me | Theorems.Thm_NumberField_finsum_finrank_adicCompletion_eq_finrank
-- name    : NumberField.finsum_finrank_adicCompletion_eq_finrank
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:26.169949+00:00
-- url     : https://prove2.me/theorems/3feb9f8c-91d8-48db-b602-eb1adcd2ecca
-- title:
--   Degree formula $\sum_{w\mid v}[K_w:F_v]=[K:F]$ at a finite place
-- statement:
--   Let $K/F$ be a finite extension of number fields, let $v$ be a finite place of $F$, i.e. a nonzero prime ideal of $\mathcal O_F$, and let $F_v$ be the $v$-adic completion of $F$. For each prime $w$ of $\mathcal O_K$ lying over $v$ (written $w \mid v$), let $K_w$ be the $w$-adic completion of $K$, regarded as an $F_v$-algebra via the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$. Then
--
--   $$
--   \sum_{w \mid v} [K_w : F_v] \;=\; [K : F].
--   $$
--
--   This is the fundamental local–global degree identity (equivalently $\sum_{w\mid v} e_w f_w = [K:F]$ read through the completions). It is what makes local norms of elements coming from $F_v$ multiply up to the global degree, e.g. $\prod_{w\mid v} N_{K_w/F_v}(a) = a^{[K:F]}$ for $a \in F_v$.
--
--   **Formalization Note** Mathlib at this revision provides no canonical algebra structure $F_v \to K_w$. As in Mathlib's own `NumberField.HeightOneSpectrum` API (the instance `Module.Finite Kv Lw` in `NumberField/Completion/FinitePlace.lean`), the statement takes, for each $w$, an arbitrary $F_v$-algebra structure on $K_w$ that is continuous (`ContinuousSMul`) and compatible with $F \to K$ (`IsScalarTower F F_v K_w`). Since $F$ is dense in $F_v$, such a structure is unique, and it exists (the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$) exactly when $w \mid v$; so the hypotheses just name the canonical embedding. Primes $w \mid v$ are the height-one primes $w$ of $\mathcal O_K$ with `w.asIdeal.LiesOver v.asIdeal`; there are finitely many, and the finite sum/product is written with `finsum`/`finprod` so that no finiteness hypothesis is needed.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der math. Wiss. 322, Springer 1999, Chapter II, §8, Corollary (8.4) (consequence of Proposition (8.3) $K\otimes_F F_v \cong \prod_{w\mid v}K_w$); finite-place case, with $K/F$ separable since char 0.

import Mathlib

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField

theorem finsum_finrank_adicCompletion_eq_finrank {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F))
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Algebra (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      ContinuousSMul (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      IsScalarTower F (v.adicCompletion F) (w.1.adicCompletion K)] :
    ∑ᶠ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion K) = Module.finrank F K := by sorry

end NumberField
