-- Prove2me | Theorems.Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift
-- name    : LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/119bdfe9-c4d4-586d-b5a3-49a98afb36d7
-- title:
--   Adelic weight-one lift is a Hecke coset eigenfunction
-- statement:
--   Fix a nonzero natural number $n$ and a function $f:\mathfrak H\to\mathbb C$ invariant under the weight-$1$ slash action of every $\varepsilon\in\Gamma_1(n)$, and let $\chi$ be a Dirichlet character modulo $n$ with values in $\mathbb C$ such that $f\mid_1\gamma=\chi(d)\,f$ for every $\gamma\in\Gamma_0(n)$, where $d=\gamma_{11}$ is the lower-right entry read in $\mathbb Z/n$. Let $\Phi$ be a Hecke eigensystem over $\mathbb Q$ with complex coefficients, i.e. a nonzero level ideal of $\mathcal O_{\mathbb Q}$ together with families $a,b$ indexed by the height-one primes, and assume $\Phi.\mathrm{level}=(n)$. Let $S$ be a finite set of height-one primes $v$ of $\mathcal O_{\mathbb Q}$ such that every $v\notin S$ fails to divide $(n)$, and assume that for every $v\notin S$, writing $p=\mathrm{absNorm}(v)$, the classical weight-one identity $\sum_{j<p} f\mid_1\begin{pmatrix}1&j\\0&p\end{pmatrix}+\chi(p)\,\bigl(f\mid_1\mathrm{diag}(p,1)\bigr)=\Phi.a(v)\,f$ holds, the two matrix families being [`ModularForm.heckeMatrix`](def/ModularForm_HeckeOperator.html#L18) and [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21). The conclusion is that for every $v\notin S$ the adelic function $\varphi=$ `weightOneLift` $((n))\,f$ on $\mathrm{GL}_2$ of the adeles of $\mathbb Q$ — which sends $g$ to $(f\mid_1 h_\infty)(i)\cdot\det h_\infty$ for a chosen decomposition $g=\gamma\,h\,u$ with $\gamma$ rational, $u$ in the level subgroup $((\text{productionPinsCompact }\mathbb Q).U\,(n))$, $h$ trivial at the finite places and with archimedean part $h_\infty$ of positive determinant, and to $0$ when no such decomposition exists — satisfies `IsHeckeCosetEigenfunctionAt` for the subgroup $U=(\text{productionPinsCompact }\mathbb Q).U\,\Phi.\mathrm{level}$, the generator $g_v=(\text{productionPinsCompact }\mathbb Q).\mathrm{gen}\,v$ and eigenvalue $\Phi.a(v)$: there are $\mathrm{absNorm}(v)+1$ elements lying in the double coset $Ug_vU$, covering it and pairwise distinct modulo $U$ on the right, whose associated coset sum $g\mapsto\sum_i\varphi(g\,r_i)$ equals $\Phi.a(v)\,\varphi(g)$ for all $g$.
--
--   This is the classical-to-adelic dictionary for Hecke operators in weight one: the $p+1$ left cosets of the double coset of $\mathrm{diag}(\varpi_v,1)$ match the $p$ matrices $\begin{pmatrix}1&j\\0&p\end{pmatrix}$ defining $U_p$ together with one further coset on which the $\Gamma_0(n)$-transformation law contributes $\chi(p)$. It is used in the construction of the adelic realisation of a dihedral weight-one primitive form, namely by [`DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm`](thm.html#DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm) and [`DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm`](thm.html#DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.lean

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain AutomorphicForm.SmoothCusp
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ) (hΦ : Φ.level = Ideal.span {(n : 𝓞 ℚ)})
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
          + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
              (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = Φ.a v • f) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      IsHeckeCosetEigenfunctionAt ℚ ((productionPinsCompact ℚ).U Φ.level)
        ((productionPinsCompact ℚ).gen v) v (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (Φ.a v) := by sorry
