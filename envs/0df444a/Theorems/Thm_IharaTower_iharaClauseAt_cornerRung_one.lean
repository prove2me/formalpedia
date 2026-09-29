-- Prove2me | Theorems.Thm_IharaTower_iharaClauseAt_cornerRung_one
-- name    : IharaTower.iharaClauseAt_cornerRung_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/b583057d-1ba5-5bc5-8b53-10fe7945b43a
-- title:
--   Ihara clause for a one-leg corner rung
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a domain), let $V,V'$ be $\mathcal{O}$-modules, and let $\mathbb{T},\mathbb{T}'$ be commutative $\mathcal{O}$-algebras acting on $V$ and $V'$ respectively, compatibly with the $\mathcal{O}$-actions. Let $S$ and $S'$ be idempotent splittings of $\mathbb{T}$ and $\mathbb{T}'$ — finite families of complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals, with $e_i\in\mathfrak{m}_j$ exactly when $i\neq j$ — and fix indices $i_0$, $i_0'$. Write $T=S.\mathrm{CornerRing}\,i_0$, $T'=S'.\mathrm{CornerRing}\,i_0'$, and $M$, $M'$ for the corner submodules $e_{i_0}V$, $e_{i_0'}V'$, each assumed finite and free over $\mathcal{O}$, and equipped with level pairings $P$, $P'$: $\mathcal{O}$-bilinear forms $B$ with values in $\mathcal{O}$ that are self-adjoint for the corner-ring action and perfect (bijective as maps $M\to M^{*}$). Given $\mathcal{O}$-linear maps $i_\alpha:M\to M'$ and $j_\alpha:M'\to M$ with $P.B(j_\alpha m',m)=P'.B(m',i_\alpha m)$ and $j_\alpha\circ i_\alpha=\Delta_0\cdot$ for some $\Delta_0\in T$, an $\mathcal{O}$-algebra map $\mathrm{res}:T'\to T$, an $\mathcal{O}$-algebra map $\pi_T:T\to\mathcal{O}$, an irreducible $\varpi\in\mathcal{O}$, and assuming: (i) $i_\alpha v\in\varpi M'$ implies $v\in\varpi M$; (ii) $j_\alpha(t'\cdot m')=\mathrm{res}(t')\cdot j_\alpha(m')$; (iii) the $\mathcal{O}$-submodule $\ker(\pi_T\circ\mathrm{res})\cdot M'$ is saturated, i.e. $a\,m'$ lying in it with $a\neq 0$ forces $m'$ to lie in it; (iv) $\operatorname{finrank}_\mathcal{O}M'[\ker(\pi_T\circ\mathrm{res})]\le\operatorname{finrank}_\mathcal{O}M[\ker\pi_T]$. Then $i_\alpha$ carries the torsion submodule $M[\ker\pi_T]$ onto $M'[\ker(\pi_T\circ\mathrm{res})]$, and there is a one-leg `LegDatum` $L$ for $P,P'$ with $L.\mathrm{iLeg}=![i_\alpha]$, $L.\mathrm{jLeg}=![j_\alpha]$, $L.\mathrm{table}=![![\Delta_0]]$ such that the corner rung assembled from $L$ with coefficient vector $![1]$ and $\mathrm{res}$ satisfies `IharaClauseAt` at $(\pi_T,\pi_T\circ\mathrm{res})$ (the same image equality for the rung's $i$) and `IsIharaDataAt`, i.e. the preimage under the rung's $j$ of $\ker\pi_T\cdot M$ equals $\ker(\pi_T\circ\mathrm{res})\cdot M'$.
--
--   This is the single-leg specialisation of the corner-rung form of Ihara's lemma used in the Taylor–Wiles ladder: a degeneracy pair between two Hecke corner modules, satisfying a saturation condition and a rank inequality, produces a rung datum whose $i$ maps $\pi_T$-torsion onto $\pi_T\circ\mathrm{res}$-torsion and whose $j$ pulls cotorsion back to cotorsion. It is invoked in the construction of a Hecke-module rung at a prime whose residue characteristic unit root is used when no cube divides the relevant level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_iharaClauseAt_cornerRung_one.lean

import Mathlib
import Definitions.Def_HeckeModule_IharaDataAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaLemma IharaTower IharaTower.RungAssembly

theorem IharaTower.iharaClauseAt_cornerRung_one
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
    (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
    (P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀)))
    (P' : IharaTower.LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (iα : ↥(cornerSubmodule (M := V) (S.e i₀)) →ₗ[𝒪] ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (jα : ↥(cornerSubmodule (M := V') (S'.e i₀')) →ₗ[𝒪] ↥(cornerSubmodule (M := V) (S.e i₀)))
    (Δ₀ : S.CornerRing i₀)
    (hadj : ∀ (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))) (m : ↥(cornerSubmodule (M := V) (S.e i₀))),
      P.B (jα m') m = P'.B m' (iα m))
    (hji : ∀ m : ↥(cornerSubmodule (M := V) (S.e i₀)), jα (iα m) = Δ₀ • m)
    (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀) (πT : S.CornerRing i₀ →ₐ[𝒪] 𝒪)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : ↥(cornerSubmodule (M := V) (S.e i₀))) (x : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      iα v = ϖ • x → ∃ v₁, v = ϖ • v₁)
    (hjeq : ∀ (t' : S'.CornerRing i₀') (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), jα (t' • m') = res t' • jα m')
    (hsat' : ∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), a ≠ 0 →
      a • m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪 →
      m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
          ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪)
      ≤ Module.finrank 𝒪
        ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
          ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    Submodule.map iα ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
        ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪 ∧
    ∃ L : LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
        (M := ↥(cornerSubmodule (M := V) (S.e i₀))) (M' := ↥(cornerSubmodule (M := V') (S'.e i₀'))) (𝒪 := 𝒪) P P' 1,
      L.iLeg = ![iα] ∧ L.jLeg = ![jα] ∧ L.table = ![![Δ₀]] ∧
      IharaTower.IharaClauseAt (IharaTower.cornerRung S S' i₀ i₀' P P' L ![1] res) πT (πT.comp res) ∧
      IharaTower.IsIharaDataAt (IharaTower.cornerRung S S' i₀ i₀' P P' L ![1] res) πT (πT.comp res) := by sorry
