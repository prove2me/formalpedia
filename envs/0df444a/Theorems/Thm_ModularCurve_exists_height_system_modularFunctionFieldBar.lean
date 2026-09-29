-- Prove2me | Theorems.Thm_ModularCurve_exists_height_system_modularFunctionFieldBar
-- name    : ModularCurve.exists_height_system_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/06175ca4-541f-5107-a31e-384e23fb47a4
-- title:
--   Height-bounded linear system cutting out Riemann–Roch spaces on X₀(N)
-- statement:
--   Fix $N\ge 1$ and a number field $K$ realised as a finite-dimensional intermediate field of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` over $\mathbb{Q}$, natural numbers $g'\le g''$, and a family $b_0,\dots,b_{n-1}$ in $\overline{F}_N:=$ `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb{Q}}$-Laurent series obtained by base change of `modularFunctionFieldFull N` along $\mathbb{Q}\to\overline{\mathbb{Q}}$. Write $J$ for the element of $\overline{F}_N$ given by the coefficientwise image `coeffEmb` of the $q$-expansion `jq`. Assume: each $b_i$ is fixed by the coefficientwise Galois action `arithmeticGalois` of every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; the $b_i$ are linearly independent over $\overline{\mathbb{Q}}[J]$, in the sense that $\sum_i c_i(J)b_i=0$ with $c_i\in\overline{\mathbb{Q}}[X]$ forces all $c_i=0$; and each $x\in\overline{F}_N$ admits $q\ne 0$ and $c_i$ in $\overline{\mathbb{Q}}[X]$ with $x\cdot q(J)=\sum_i c_i(J)b_i$. Then there are natural numbers $m$ (`mdeg`), $r$ (`rdim`), $d$ (`qdeg`) and reals $\alpha\ge 0$, $\beta$, independent of what follows, such that for every divisor $D$ on the places of $\overline{F}_N$ over $\overline{\mathbb{Q}}$ and every degree-zero divisor $E$ with $D$ effective, $D=E+g''\cdot[\overline{\infty}]$ where $\overline{\infty}=$ `cuspInftyBar N`, $D$ fixed by `arithmeticGalois` for all $\sigma$ in the fixing subgroup of $K$, and all entries of the symmetrised coordinate vector $\mathrm{symVec}\,N\,g''\,D$ (the coefficients, in positions $g''-k$, of the product $\prod_v (\mathrm{jFactor}\,N\,v)^{(Dv)^+}$) lying in $K$, there exist a nonzero $q_K\in K[X]$ with $\deg q_K\le d$ and a matrix $M$ of size $r\times(n\times(m+1))$ over $K$ such that the logarithmic height of the entries of $M$ is at most $\alpha$ times the logarithmic height of $\mathrm{symVec}\,N\,g''\,D$ (read in $K$) plus $\beta$, and such that, setting $f_u=\bigl(\sum_i\bigl(\sum_{e\le m}u(i,e)J^{e}\bigr)b_i\bigr)\cdot q_K(J)^{-1}$ for $u:\mathrm{Fin}\,n\times\mathrm{Fin}(m+1)\to\overline{\mathbb{Q}}$: (i) for nonzero $u$, $M$ base-changed to $\overline{\mathbb{Q}}$ kills $u$ if and only if $0\le (D-(g''-g')[\overline{\infty}])(v)+v.\mathrm{ord}(f_u)$ at every place $v$; and (ii) every nonzero $f\in\overline{F}_N$ with $0\le (D-(g''-g')[\overline{\infty}])(v)+v.\mathrm{ord}(f)$ at all $v$ equals $f_u$ for some nonzero $u$.
--
--   This packages the Riemann–Roch space $L(D-(g''-g')\overline{\infty})$ on the modular curve of level $N$ over $\overline{\mathbb{Q}}$ as the kernel of an explicit matrix over the base field $K$, with the height of that matrix bounded linearly in the naive height of $D$ (the height of its symmetrised $j$-coordinate vector), uniformly in $D$. It is used in the reduction step [`ModularCurve.JZero.naiveHeight_reduce`](thm.html#ModularCurve.JZero.naiveHeight_reduce).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_height_system_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_height_system_modularFunctionFieldBar (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' g'' : ℕ) (hle : g' ≤ g'') (n : ℕ) (b : Fin n → modularFunctionFieldBar N)
    (hbQ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • b i = b i)
    (hbli : ∀ c : Fin n → Polynomial (AlgebraicClosure ℚ),
      (∑ i : Fin n, Polynomial.aeval
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
            (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) = 0
        → ∀ i, c i = 0)
    (hbsp : ∀ x : modularFunctionFieldBar N, ∃ (q : Polynomial (AlgebraicClosure ℚ))
        (c : Fin n → Polynomial (AlgebraicClosure ℚ)), q ≠ 0 ∧
        x * Polynomial.aeval
            (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) q
          = ∑ i : Fin n, Polynomial.aeval
              (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) :
    ∃ (mdeg rdim qdeg : ℕ) (α β : ℝ), 0 ≤ α ∧
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        ∀ hmem : ∀ k, symVec N g'' D k ∈ K,
        ∃ qK : Polynomial K, qK ≠ 0 ∧ qK.natDegree ≤ qdeg ∧
        ∃ Msys : Matrix (Fin rdim) (Fin n × Fin (mdeg + 1)) K,
          Height.logHeight (fun ij : Fin rdim × (Fin n × Fin (mdeg + 1)) => Msys ij.1 ij.2)
            ≤ α * Height.logHeight (fun k : Fin (g'' + 1) => (⟨symVec N g'' D k, hmem k⟩ : K)) + β ∧
          (∀ u : Fin n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 →
            ((Msys.map (algebraMap K (AlgebraicClosure ℚ))).mulVec u = 0 ↔
              ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
                0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v
                  + v.ord ((∑ i : Fin n, Polynomial.aeval
                        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                          (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                        (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
                        * b i)
                      * (Polynomial.aeval
                          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                            (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                          (qK.map (algebraMap K (AlgebraicClosure ℚ))))⁻¹))) ∧
          (∀ f : modularFunctionFieldBar N, f ≠ 0 →
            (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
              0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                    : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v + v.ord f) →
            ∃ u : Fin n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 ∧
              (∑ i : Fin n, Polynomial.aeval
                  (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                    (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                  (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ))
                  * b i)
                * (Polynomial.aeval
                    (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
                      (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
                    (qK.map (algebraMap K (AlgebraicClosure ℚ))))⁻¹ = f) := by sorry
