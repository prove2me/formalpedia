-- Prove2me | Theorems.Thm_NumberField_eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi
-- name    : NumberField.eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7c0866f9-f7f3-5cc9-828d-b5e580a7808c
-- title:
--   A diag(varpi,1) Hecke coset system has N(w)+1 members
-- statement:
--   Let $L$ be a number field, let $w$ be a height-one prime of the ring of integers $\mathcal{O}_L$, and write $L_w$ for the $w$-adic completion of $L$ and $\mathcal{O}_w$ for its valuation subring. Let $\varpi \in \mathcal{O}_w$ be irreducible and assume its image in $L_w$ is nonzero. Let $U \le \mathrm{GL}_2(L_w)$ be the image of $\mathrm{GL}_2(\mathcal{O}_w)$ under the map induced by $\mathcal{O}_w \to L_w$ (the range of `Matrix.GeneralLinearGroup.map` applied to the structure map), and let $g \in \mathrm{GL}_2(L_w)$ be the invertible matrix $\begin{pmatrix}\varpi&0\\0&1\end{pmatrix}$, with inverse given by $\varpi^{-1}$ in the upper-left entry. Let $n$ be a natural number and $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ a family satisfying the three conditions of `IsHeckeCosetSystem` for $U$ and $g$: every $rT\,i$ lies in the double coset $U \cdot \{g\} \cdot U$; every element of that double coset lies in the same left coset $xU$ in $\mathrm{GL}_2(L_w)/U$ as some $rT\,i$; and $i \mapsto rT\,i \bmod U$ is injective. The conclusion is $n = \mathrm{absNorm}(w) + 1$, where $\mathrm{absNorm}(w)$ is the absolute norm (cardinality of $\mathcal{O}_L/w$) of the prime ideal attached to $w$.
--
--   This is the classical count of the left cosets occurring in the Hecke double coset of $\mathrm{diag}(\varpi,1)$ for $\mathrm{GL}_2$ over a local field, the cosets being parametrised by $\mathbb{P}^1(\mathcal{O}_w/\varpi)$, which has $N(w)+1$ points. It is used in the bookkeeping of Hecke words, in the Satake-type combination identity at places of residue degree one and in the orbital-integral bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.eq_absNorm_add_one_of_isHeckeCosetSystem_diagPi
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (ϖ : w.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT) :
    n = Ideal.absNorm w.asIdeal + 1 := by sorry
