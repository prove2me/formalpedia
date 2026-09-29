-- Prove2me | Theorems.Thm_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
-- name    : IharaTower.exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/cad6b0af-6cd1-534f-a033-ad812d65e76d
-- title:
--   Residual injectivity of combined raising at diamond-invariant corner
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain, let $N,q$ be non-zero naturals with $Nq$ non-zero, $q$ prime and $q\nmid N$, and let $H\le(\mathbb Z/N)^\times$, $H'\le(\mathbb Z/Nq)^\times$ be subgroups admitting level data [`CohCarrier.LevelLE`](def/CohCarrier_Level.html#L330) at $d=1$ and at $d=q$, i.e. $N\mid Nq$, $d\mid Nq/N$, and reduction $(\mathbb Z/Nq)^\times\to(\mathbb Z/N)^\times$ carries $H'$ into $H$. Write $H^1(M,H,A)$ for the group $\mathrm{Hom}(\Gamma_H(M),A)$ of additive characters of $\Gamma_H(M)$, and let $\mathbb T,\mathbb T'$ be commutative $\mathcal O$-algebras acting on $H^1(N,H,\mathcal O)$ and $H^1(Nq,H',\mathcal O)$ compatibly with $\mathcal O$. Fix corner data $cd$, $cd'$ for these two modules (an idempotent splitting with a chosen index and a pairing), with corner rings and corner submodules $M=cd.\mathrm{cornerModule}$, $M'=cd'.\mathrm{cornerModule}$, both free over $\mathcal O$, and a two-leg degeneracy descent $D$: two $\mathcal O$-linear maps each way preserving the corners, whose raising maps are assumed to be the degeneracy pull-backs $\iota_1^*$ and $\iota_q^*$ given by [`CohCarrier.iDegL`](def/CohCarrier_Level.html#L401); together with a composition table in the lower corner ring, adjointness of the legs for the two pairings, and the identity $j_k\circ i_{k'}=\mathrm{table}\,k\,k'$ on the lower corner. Let $c:\{0,1\}\to cd.\mathrm{cornerRing}$ and let $\varpi$ be an irreducible element of $\mathcal O$. Assume: (i) if $v\in M$ satisfies $c_k\cdot v\in\varpi M$ for both $k$, then $v\in\varpi M$; (ii) for a prime $\ell_0\nmid Nq$, any $v\in M$ with $T_{\ell_0}v-(\ell_0+1)v$ in $\varpi\,H^1(N,H,\mathcal O)$ lies in $\varpi M$; (iii) Ihara's lemma in kernel-pair form for diamond-invariant residual classes: if $g,h\in H^1(N,H,\mathcal O/\varpi)$ satisfy $\langle\sigma\rangle g=g$ and $\langle\sigma\rangle h=h$ for all $\sigma\in\Gamma_0(N)$ (the action [`CohCarrier.diamondRaw`](def/CohCarrier_Level.html#L291) by conjugation) and $\iota_1^*g+\iota_q^*h=0$, then both $g$ and $h$ are Eisenstein at $\ell_0$, i.e. $T_{\ell_0}$ acts on each as $\ell_0+1$; (iv) every $v\in M$ is diamond-invariant over $\mathcal O$. The conclusion: for all $v\in M$ and $x\in M'$, if the combined raising map $\sum_k i_k(c_k\cdot v)=\iota_1^*(c_0v)+\iota_q^*(c_1v)$ equals $\varpi x$, then $v\in\varpi M$.
--
--   This is the residual-injectivity clause supplied to the Ihara rung datum of the tower: Ihara's lemma at the auxiliary prime $q$, in kernel-pair form and for diamond-invariant classes, combined with a non-Eisenstein hypothesis at $\ell_0$ and residual injectivity of the coefficient vector, yields that the combined level-raising map is injective modulo $\varpi$ on the chosen corner. It is used in the construction of a Hecke-module rung at the residue characteristic, [`CuspForm.heckeLocal.exists_heckeModule_rung_at_residueChar_unitRoot_of_cornerData_of_fullCorner_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.exists_heckeModule_rung_at_residueChar_unitRoot_of_cornerData_of_fullCorner_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant.lean

import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Tower
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaLemma IharaTower

theorem IharaTower.exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)] (hq : q.Prime) (hqN : ¬ q ∣ N)
    {H : Subgroup (ZMod N)ˣ} {H' : Subgroup (ZMod (N * q))ˣ}
    (h₁ : CohCarrier.LevelLE N (N * q) H H' 1) (hq' : CohCarrier.LevelLE N (N * q) H H' q)
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (CohCarrier.H1 N H 𝒪)] [Module 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 N H 𝒪)] [IsScalarTower 𝒪 𝕋' (CohCarrier.H1 (N * q) H' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N H 𝒪 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) H' 𝒪 𝕋')
    (D : DegeneracyDescent (𝒪 := 𝒪) cd cd' 2)
    (hD : D.iRaw = ![CohCarrier.iDegL N (N * q) H H' 1 𝒪 𝒪 h₁, CohCarrier.iDegL N (N * q) H H' q 𝒪 𝒪 hq'])
    (table : Fin 2 → Fin 2 → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin 2) (m : cd.cornerModule), D.jLeg k (D.iLeg k' m) = table k k' • m)
    (c : Fin 2 → cd.cornerRing)
    [Module.Free 𝒪 cd.cornerModule] [Module.Free 𝒪 cd'.cornerModule]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)

    (hc : ∀ v : cd.cornerModule, (∀ k, ∃ w : cd.cornerModule, c k • v = ϖ • w) → ∃ v₁, v = ϖ • v₁)

    (ℓ₀ : ℕ) [NeZero ℓ₀] (hℓ : ℓ₀.Prime) (hℓN : ¬ ℓ₀ ∣ N * q)
    (hne : ∀ v : cd.cornerModule,
      CohCarrier.heckeT N H ℓ₀ 𝒪 (v : CohCarrier.H1 N H 𝒪) - ((ℓ₀ : 𝒪) + 1) • (v : CohCarrier.H1 N H 𝒪)
        ∈ (Ideal.span {ϖ} • ⊤ : Submodule 𝒪 (CohCarrier.H1 N H 𝒪)) → ∃ v₁ : cd.cornerModule, v = ϖ • v₁)

    (hihara : ∀ g h : CohCarrier.H1 N H (𝒪 ⧸ Ideal.span {ϖ}),
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ g = g) →
      (∀ σ : CongruenceSubgroup.Gamma0 N, CohCarrier.diamondRaw N H (𝒪 ⧸ Ideal.span {ϖ}) σ h = h) →
      CohCarrier.iDeg' N (N * q) H H' 1 (𝒪 ⧸ Ideal.span {ϖ}) h₁ g +
          CohCarrier.iDeg' N (N * q) H H' q (𝒪 ⧸ Ideal.span {ϖ}) hq' h = 0 →
        CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ g ∧ CohCarrier.IsEis 𝒪 (𝒪 ⧸ Ideal.span {ϖ}) N H ℓ₀ h)

    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 N) (v : cd.cornerModule),
      CohCarrier.diamondRaw N H 𝒪 σ (v : CohCarrier.H1 N H 𝒪) = (v : CohCarrier.H1 N H 𝒪)) :
    ∀ (v : cd.cornerModule) (x : cd'.cornerModule),
      RungAssembly.iComb (D.toLegDatum table adjoint_leg htable) c v = ϖ • x → ∃ v₁, v = ϖ • v₁ := by sorry
