-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/54b83beb-028d-582b-86ad-a47ba3ceacda
-- title:
--   Non-zero Whittaker functional on a GL₃ principal series
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $K_v :=$ `v.adicCompletion ℚ` is the corresponding completion, and write $G = \mathrm{GL}_3(K_v)$. Let $\chi_0,\chi_1,\chi_2$ be multiplicative characters $K_v^\times \to \mathbb{C}^\times$, each locally constant as a function on $K_v^\times$, and let $\psi$ be an additive character of $K_v$ with values in $\mathbb{C}$ for which there exists $m \in \mathbb{Z}$ with $\psi(x) = 1$ whenever $v(x) \le \exp m$ in the value group. Let $I(\chi) \subseteq (G \to \mathbb{C})$ be the $\mathbb{C}$-subspace of locally constant functions $f$ satisfying $f(n(x,y,z)g) = f(g)$ for all $x,y,z \in K_v$ and $g \in G$, where $n(x,y,z)$ is the unipotent matrix with rows $(1,x,z)$, $(0,1,y)$, $(0,0,1)$, and $f(\mathrm{diag}(a_0,a_1,a_2)g) = \bigl(\prod_i \chi_i(a_i)\bigr)\cdot (\|a_0\|/\|a_2\|)\cdot f(g)$ for all $a_i \in K_v^\times$ (the normalising factor being the ratio of norms itself, not its square root). The assertion is that there exists a $\mathbb{C}$-linear form $L : I(\chi) \to \mathbb{C}$ with $L \ne 0$ and $L\bigl(g \mapsto F(g\,n(x,y,z))\bigr) = \psi(x+y)\,L(F)$ for all $x,y,z \in K_v$ and all $F \in I(\chi)$.
--
--   This is the existence half of the local Whittaker-model theorem for principal series of $\mathrm{GL}_3$ over a non-archimedean completion of $\mathbb{Q}$; uniqueness of $L$ up to scalars is not asserted here. It is used in the construction of the coefficient function realising a suitable coset eigenfunction inside $I(\chi)$, in [`LanglandsTunnell.CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_ne_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψball : ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp m → ψv x = 1) :
    ∃ L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ, L ≠ 0 ∧ IsWhittakerFunctional3 ψv L := by sorry
