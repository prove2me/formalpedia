-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
-- name    : LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5f231cc1-e001-56dd-9632-2334785969de
-- title:
--   Whittaker transformation law for the GL₃ coefficient
-- statement:
--   Work over $\mathbb{Q}$, with $\mathbb{A}$ the adele ring of $\mathbb{Q}$ (the adele ring of $\mathcal{O}_{\mathbb{Q}}$ in $\mathbb{Q}$). Fix a subset $D$ of the adelic group $\mathrm{GL}_2(\mathbb{A})$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A})$ indexed by the ideals of $\mathcal{O}_{\mathbb{Q}}$, and a family `gen` of elements of $\mathrm{GL}_2(\mathbb{A})$ indexed by the height-one primes of $\mathcal{O}_{\mathbb{Q}}$. Let $\psi$ be an additive character $\mathbb{A} \to \mathbb{C}$ which is trivial on the rationals, i.e. $\psi(\alpha) = 1$ for every $\alpha \in \mathbb{Q}$ viewed in $\mathbb{A}$, and let $\Phi : \mathrm{GL}_3(\mathbb{A}) \to \mathbb{C}$ satisfy $\Phi(n(x,y,z)g) = \Phi(g)$ for all rational $x, y, z$ and all $g \in \mathrm{GL}_3(\mathbb{A})$, where $n(x,y,z)$ denotes the upper unipotent matrix with entries $x$, $y$, $z$ in positions $(1,2)$, $(2,3)$, $(1,3)$. Let $W$ be the Whittaker coefficient $$W(g) = \int\!\!\int\!\!\int \Phi(n(x,y,z)g)\,\psi(-(x+y))\,d\nu(x)\,d\nu(y)\,d\nu(z),$$ the measure $\nu$ being the additive Haar measure of $\mathbb{A}$ conditioned on the adelic box (a fundamental domain for the archimedean lattice times the integral finite adeles), as packaged by the carrier pins `productionPinsOf` built from $D$, $U$ and `gen`. The conclusion is that $W$ satisfies the $\psi$-Whittaker transformation law: $W(n(x,y,z)g) = \psi(x+y)\,W(g)$ for all $x, y, z \in \mathbb{A}$ and all $g \in \mathrm{GL}_3(\mathbb{A})$. The auxiliary data $D$, $U$ and `gen` enter only through the pins, of which the Whittaker integral uses only the measurable structure and the conditioned Haar measure on $\mathbb{A}$.
--
--   This is the standard equivariance of a Whittaker coefficient on $\mathrm{GL}_3$ under the upper unipotent subgroup, for the character $n(x,y,z) \mapsto \psi(x+y)$, here for the particular adelic integral used in the project. It feeds the construction of cubic induction data in the Langlands–Tunnell part of the argument, being cited by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g) :
    IsGL3PsiWhittakerFn ψ (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ) := by sorry
