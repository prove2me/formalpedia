-- Prove2me | Theorems.Thm_NumberField_norm_mem_adicCompletionIntegers
-- name    : NumberField.norm_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:29.175723+00:00
-- url     : https://prove2.me/theorems/243ccd74-7c05-4371-a4d4-42dd2b29cc7d
-- title:
--   Local norms of $w$-adic integers are $v$-adic integers
-- statement:
--   Let $K/F$ be a finite extension of number fields, let $v$ be a finite place of $F$ and $w$ a finite place of $K$, with completions $F_v$ and $K_w$ and valuation rings $\mathcal O_v \subseteq F_v$, $\mathcal O_w \subseteq K_w$. Suppose $K_w$ carries an $F_v$-algebra structure which is continuous and extends $F \hookrightarrow K \hookrightarrow K_w$ (this happens exactly when $w \mid v$). Then for every $z \in \mathcal O_w$,
--
--   $$
--   N_{K_w/F_v}(z) \in \mathcal O_v .
--   $$
--
--   Consequently the local norm restricts to a continuous homomorphism $\mathcal O_w^\times \to \mathcal O_v^\times$ on unit groups, which is the building block of semilocal norm maps.
--
--   **Formalization Note** The $F_v$-algebra structure on $K_w$ is a hypothesis (`Algebra`, `ContinuousSMul`, `IsScalarTower F F_v K_w`), as in Mathlib's `NumberField/Completion/FinitePlace.lean`; it is unique when it exists.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der math. Wiss. 322, Springer 1999, Chapter II, §4, Theorem (4.8) ($|\alpha|_w = |N_{K_w|F_v}(\alpha)|_v^{1/n}$, so $N$ maps $\mathcal O_w$ into $\mathcal O_v$); see also II §4, (4.9).

import Mathlib

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField

theorem norm_mem_adicCompletionIntegers {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    [Algebra (v.adicCompletion F) (w.adicCompletion K)]
    [ContinuousSMul (v.adicCompletion F) (w.adicCompletion K)]
    [IsScalarTower F (v.adicCompletion F) (w.adicCompletion K)]
    {z : w.adicCompletion K} (hz : z ∈ w.adicCompletionIntegers K) :
    Algebra.norm (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by sorry

end NumberField
