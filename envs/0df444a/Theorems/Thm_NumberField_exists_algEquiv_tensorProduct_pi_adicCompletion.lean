-- Prove2me | Theorems.Thm_NumberField_exists_algEquiv_tensorProduct_pi_adicCompletion
-- name    : NumberField.exists_algEquiv_tensorProduct_pi_adicCompletion
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:28.28746+00:00
-- url     : https://prove2.me/theorems/a2c5e2ff-6af2-4e5c-beaa-ba6943a6ff92
-- title:
--   $F_v\otimes_F K\cong\prod_{w\mid v}K_w$ for number fields
-- statement:
--   Let $K/F$ be a finite extension of number fields, let $v$ be a finite place of $F$, i.e. a nonzero prime ideal of $\mathcal O_F$, and let $F_v$ be the $v$-adic completion of $F$. For each prime $w$ of $\mathcal O_K$ lying over $v$ (written $w \mid v$), let $K_w$ be the $w$-adic completion of $K$, regarded as an $F_v$-algebra via the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$. Then the canonical map is an isomorphism of $F_v$-algebras:
--
--   $$
--   F_v \otimes_F K \;\xrightarrow{\;\sim\;}\; \prod_{w \mid v} K_w, \qquad a \otimes x \longmapsto (a\,x)_{w \mid v}.
--   $$
--
--   Precisely: there is an $F_v$-algebra isomorphism $e$ with $e(1 \otimes x) = (x)_{w\mid v}$ for all $x \in K$ (which, together with $F_v$-linearity, determines $e$). This is the structural result behind the degree formula $\sum_{w\mid v}[K_w:F_v] = [K:F]$ and the local–global formulas for norm and trace.
--
--   **Formalization Note** Mathlib at this revision provides no canonical algebra structure $F_v \to K_w$. As in Mathlib's own `NumberField.HeightOneSpectrum` API (the instance `Module.Finite Kv Lw` in `NumberField/Completion/FinitePlace.lean`), the statement takes, for each $w$, an arbitrary $F_v$-algebra structure on $K_w$ that is continuous (`ContinuousSMul`) and compatible with $F \to K$ (`IsScalarTower F F_v K_w`). Since $F$ is dense in $F_v$, such a structure is unique, and it exists (the continuous extension of $F \hookrightarrow K \hookrightarrow K_w$) exactly when $w \mid v$; so the hypotheses just name the canonical embedding. Primes $w \mid v$ are the height-one primes $w$ of $\mathcal O_K$ with `w.asIdeal.LiesOver v.asIdeal`; there are finitely many, and the finite sum/product is written with `finsum`/`finprod` so that no finiteness hypothesis is needed.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der math. Wiss. 322, Springer 1999, Chapter II, §8, Proposition (8.3): $L\otimes_K K_v \cong \prod_{w\mid v} L_w$ for finite separable $L|K$ (finite-place case, number fields).

import Mathlib

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField

theorem exists_algEquiv_tensorProduct_pi_adicCompletion {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F))
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      Algebra (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      ContinuousSMul (v.adicCompletion F) (w.1.adicCompletion K)]
    [∀ w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal},
      IsScalarTower F (v.adicCompletion F) (w.1.adicCompletion K)] :
    ∃ e : v.adicCompletion F ⊗[F] K ≃ₐ[v.adicCompletion F]
        ((w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal}) → w.1.adicCompletion K),
      ∀ x : K, e (1 ⊗ₜ x) = fun w : {w : HeightOneSpectrum (𝓞 K) // w.asIdeal.LiesOver v.asIdeal} =>
        algebraMap K (w.1.adicCompletion K) x := by sorry

end NumberField
