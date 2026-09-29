-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/8f34195f-ca5a-595d-a26b-837acb356122
-- title:
--   Unique place above a local non-square in a quadratic field
-- statement:
--   Let $K$ and $K'$ be number fields with $K'$ a $K$-algebra of degree $\operatorname{finrank}_K K' = 2$, let $d \in K$ and $r \in K'$ satisfy $r^2 = d$ (image of $d$ under $K \to K'$), and assume $K'$ is generated as a $K$-algebra by $r$, i.e. $\mathrm{adjoin}_K\{r\} = \top$. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and suppose that the image of $d$ in the $v$-adic completion $K_v$ is not a square. The conclusion has two parts, both about the type of extensions of $v$, namely the height-one primes $w$ of $\mathcal{O}_{K'}$ whose contraction along $\mathcal{O}_K \to \mathcal{O}_{K'}$ is $v$. First, any two such extensions coincide (uniqueness; existence is not part of the assertion). Second, for every such extension $w$ there exists a $K_v$-algebra isomorphism between the $w$-adic completion $K'_w$ and $K_v[X]/(X^2 - d)$, the quotient being formed with $d$ taken in $K_v$.
--
--   This is the standard statement that a quadratic extension $K' = K(\sqrt{d})$ has a single place above a finite place $v$ at which $d$ is a local non-square, with completion the corresponding local quadratic field $K_v(\sqrt d)$. It provides the global quadratic model used downstream, in [`AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd`](thm.html#AutomorphicForm.exists_isNormOf_of_isField_tensor_adicCompletion_of_not_isSquare_discr_of_finrank_dvd), to realise a prescribed local quadratic extension as a completion of a quadratic extension of the global field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_and_algEquiv_adjoinRoot_of_not_isSquare
    (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (hdeg : Module.finrank K K' = 2)
    (d : K) (r : K') (hr : r ^ 2 = algebraMap K K' d) (hgen : Algebra.adjoin K {r} = ⊤)
    (v : HeightOneSpectrum (𝓞 K))
    (hd : ¬ IsSquare (algebraMap K (v.adicCompletion K) d)) :
    (∀ 𝔳 𝔳' : v.Extension (𝓞 K'), 𝔳 = 𝔳') ∧
    ∀ 𝔳 : v.Extension (𝓞 K'),
      Nonempty (𝔳.1.adicCompletion K' ≃ₐ[v.adicCompletion K]
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (algebraMap K (v.adicCompletion K) d))) := by sorry
