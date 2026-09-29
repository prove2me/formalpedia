-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong
-- name    : LanglandsTunnell.CubicInduction.exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/742e155b-e46c-5e4c-b415-a78352e91636
-- title:
--   Pure tensor Whittaker vector with local multiplicity one at S
-- statement:
--   Fix a global additive character $\psi$ of the adele ring $\mathbb{A}$ of $\mathbb{Q}$ (trivial on principal adeles, continuous and non-trivial), a finite set $S$ of finite places, a level function $a$ on the finite places, a character $\omega\colon\mathbb{A}^{\times}\to\mathbb{C}^{\times}$, a function $W$ on $GL_3(\mathbb{A})$, Hecke parameters $\mathrm{lam}1,\mathrm{lam}2$ on the finite places, and data $D\subseteq GL_2(\mathbb{A})$, $U$ and $\mathrm{gen}$ assembling the carrier pins $\mathrm{productionPinsOf}\ \mathbb{Q}\ D\ U\ \mathrm{gen}$ for the adelic box, whose measures are the Borel Haar measure on $GL_2(\mathbb{A})$ and additive adelic Haar conditioned on the box. Let $A$ be an `AutomorphyDatum31` for these data: a continuous $\varphi=A.\mathrm{form}$ on $GL_3(\mathbb{A})$, left $GL_3(\mathbb{Q})$-invariant, with central character $\omega$, of moderate growth, transforming at each $v\in S$ under the converse congruence set of level $a(v)$ by $\omega_v$ of the $(2,2)$ entry, whose $\psi$-Whittaker integral equals $W$ at points with $S$-components in those congruence sets, cuspidal along $P_{21}$ at points with $S$-components in the corresponding parabolic congruence sets, and right $GL_3(\mathbb{Z}_p)$-invariant and an eigenfunction of the two Hecke operators at each $p\notin S$ with eigenvalues $\mathrm{lam}1(p),\mathrm{lam}2(p)$. Assume moreover that $\varphi$ is cuspidal along $P_{21}$ and along $P_{12}$ at every point, and let $W_{\mathrm{arch}}$ on $GL_3(\mathbb{A}_\infty)$ and local functions $W_{\mathrm{fin},v}$ on $GL_3(\mathbb{Q}_v)$ be such that $W(g)=W_{\mathrm{arch}}(g_\infty)\prod_{v\in T}W_{\mathrm{fin},v}(g_v)$ for every $g$ with trivial components at $S$ and components in the maximal compact outside a finite $T\supseteq S$, with $W_{\mathrm{fin},v}(1)=1$ for $v\in S$ and $W_{\mathrm{arch}}\neq 0$. Then there are $\mathrm{form}$ on $GL_3(\mathbb{A})$ and local functions $W_{\mathrm{loc},v}$ such that: $\mathrm{form}$ lies in every $\mathbb{C}$-submodule of functions containing $\varphi$ and stable under right translation by the images of $GL_3(\mathbb{Q}_v)$ for $v\in S$; $\mathrm{form}$ is continuous, left $GL_3(\mathbb{Q})$-invariant, has central character $\omega$, is cuspidal along $P_{21}$ and $P_{12}$, and has moderate growth; $W_{\mathrm{loc},v}=W_{\mathrm{fin},v}$ for $v\notin S$; for each $v\in S$ the function $W_{\mathrm{loc},v}$ satisfies $W_{\mathrm{loc},v}(u(x,y,z)g)=\psi_v(x+y)W_{\mathrm{loc},v}(g)$ for the local component $\psi_v$ of $\psi$, is normalised by $W_{\mathrm{loc},v}(1)=1$, has $\psi_v$-Whittaker multiplicity one for the right-translation representation on its cyclic subspace, generates a cyclic subspace in which every non-zero element generates $W_{\mathrm{loc},v}$ back, is right invariant under some open subgroup, and its cyclic subspace has finitely spanned subspace of right invariants for every open subgroup; and finally, for every $g$ and every finite $T\supseteq S$ with $g_v$ in the maximal compact for $v\notin T$, the $\psi$-Whittaker integral of $\mathrm{form}$ at $g$ equals $W_{\mathrm{arch}}(g_\infty)\prod_{v\in T}W_{\mathrm{loc},v}(g_v)$.
--
--   This replaces a $GL_3$ automorphy datum over $\mathbb{Q}$ by a form in the span of its local translates at the places of $S$ whose Whittaker coefficient factors as a product of an archimedean factor and normalised local factors that are irreducible, smooth and admissible as cyclic right-translation modules with one-dimensional space of Whittaker functionals. It is used in the construction of cubic induction data at the bad places, through `exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_whittaker3_eq_mul_prod_hasWhittakerMultOne_of_isCuspidalAlong
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (A : AutomorphyDatum31 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ S a ω W lam1 lam2)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) A.form)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) A.form)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Wfin : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (_hfac : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g = 1) →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wfin v (componentAt3 (𝓞 ℚ) ℚ v g))
    (_h1S : ∀ v ∈ S, Wfin v 1 = 1) (_hne : Warch ≠ 0) :
    ∃ (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ),
      (∀ V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), A.form ∈ V →
        (∀ v ∈ S, ∀ (h : LocalGL3 v), ∀ f ∈ V, (fun x => f (x * localToAdelic3 v h)) ∈ V) → form ∈ V) ∧
      Continuous form ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g) ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form ∧
      IsModerateGrowth3 ℚ form ∧
      (∀ v, v ∉ S → Wloc v = Wfin v) ∧
      (∀ v ∈ S, IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v) ∧ Wloc v 1 = 1 ∧
        HasWhittakerMultOne (psiLoc ψ v) (Wloc v) ∧
        (∀ F ∈ gl3CyclicSubspace (Wloc v), F ≠ 0 → Wloc v ∈ gl3CyclicSubspace F) ∧
        (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, Wloc v (g * k) = Wloc v g) ∧
        ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
          ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (Wloc v),
            (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
        (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
        whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ form g =
          Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g) := by sorry
