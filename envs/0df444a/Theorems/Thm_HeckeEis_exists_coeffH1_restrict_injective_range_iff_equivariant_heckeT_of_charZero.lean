-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero
-- name    : HeckeEis.exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/8e9fad4e-4a4c-5b73-91c3-1c9ebc28ff5b
-- title:
--   Hecke-equivariant embedding of coefficient H¹ into Γ_{H_1}(Nq²)-cohomology
-- statement:
--   Let $N$ be a natural number, $q$ a prime, $K$ a field of characteristic zero and $W$ a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on a $K$-vector space $W_c$. Let $\mathrm{red}\colon\Gamma_0(N)\to\mathrm{GL}_2(\mathbb{Z}/q)$ be the homomorphism obtained by including $\Gamma_0(N)$ into $\mathrm{SL}(2,\mathbb{Z})$, reducing entries modulo $q$ and viewing the result in $\mathrm{GL}_2$; let $H_1\le(\mathbb{Z}/Nq^2)^\times$ be the kernel of the reduction $(\mathbb{Z}/Nq^2)^\times\to(\mathbb{Z}/q)^\times$; and let $\mathrm{conj}\colon\ker(\mathrm{red})\to\Gamma_{H_1}(Nq^2)$ be a homomorphism into the group of matrices of $\Gamma_0(Nq^2)$ whose lower-right entry lies in $H_1$, satisfying entrywise, for $x=\begin{pmatrix}a&b\\c&d\end{pmatrix}$, that $\mathrm{conj}(x)$ has entries $a$, $b/q$ (i.e. $q$ times the upper-right entry equals $b$), $qc$ and $d$. Then there is a $K$-linear map $S$ from $H^1$ of $\Gamma_0(N)$ with coefficients in $W\circ\mathrm{red}$ — the quotient of the module of functions $z\colon\Gamma_0(N)\to W_c$ with $z(gh)=z(g)+W(\mathrm{red}\,g)z(h)$ by the coboundaries — to the group of additive homomorphisms $\Gamma_{H_1}(Nq^2)\to W_c$ such that: (1) for every cocycle $z$ and every $x\in\ker(\mathrm{red})$, $S([z])$ takes the value $z(x)$ at $\mathrm{conj}(x)$; (2) $S$ is injective; (3) $\varphi$ lies in the range of $S$ exactly when $\varphi(\mathrm{conj}(\gamma y\gamma^{-1}))=W(\mathrm{red}\,\gamma)\varphi(\mathrm{conj}(y))$ for all $\gamma\in\Gamma_0(N)$ and all $y\in\ker(\mathrm{red})$ with $\gamma y\gamma^{-1}\in\ker(\mathrm{red})$; and (4) for every nonzero $\ell$ coprime to $Nq$ and with $\ell\not\equiv 0\pmod q$ there is a $K$-linear endomorphism $T$ of the coefficient $H^1$ which is a Hecke operator at $\ell$ twisted by $W(\mathrm{diag}(\ell,1))$, in the sense that each cocycle $z$ admits a cocycle $w$ equal to the transfer-type sum $\mathrm{coeffHeckeFun}$ of $z$ with $T[z]=[w]$, and which satisfies $S(Tx)=W(\mathrm{diag}(\ell,1))\circ\bigl(\mathrm{heckeT}_{N q^2,H_1,\ell}(S x)\bigr)$ for all $x$, where $\mathrm{heckeT}$ is the operator on homomorphisms on $\Gamma_{H_1}(Nq^2)$ obtained by transfer along the conjugation map $\mathrm{conjL}$.
--
--   The statement identifies group cohomology of $\Gamma_0(N)$ with coefficients in a representation of $\mathrm{GL}_2(\mathbb{F}_q)$ pulled back along reduction modulo $q$ with the subspace of conjugation-equivariant classes in the cohomology of the smaller group $\Gamma_{H_1}(Nq^2)$, compatibly with the Hecke operators at primes away from $Nq$ up to the twist by $\mathrm{diag}(\ell,1)$. It is used to transport an eigenvector functional coming from a newform cuspidal of a given type $W$ into the cohomology of $\Gamma_{H_1}(Nq^2)$, and is cited by the results producing such functionals and the corresponding eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero.lean

import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero
    (N q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K]
    {Wc : Type} [AddCommGroup Wc] [Module K Wc] (W : Representation K (CuspidalType.GL2 q) Wc)
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (H₁ : Subgroup (ZMod (N * q ^ 2))ˣ)
    (hH₁ : H₁ = (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (N * q ^ 2) H₁))
    (hconj : ∀ x : ↥red.ker,
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 = ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
      (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
        (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) :
    ∃ S : HeckeEis.coeffH1 (W.comp red) →ₗ[K] CohCarrier.H1 (N * q ^ 2) H₁ Wc,
      (∀ (z : ↥(HeckeEis.coeffCocycles (W.comp red))) (x : ↥red.ker),
        S (HeckeEis.coeffH1Mk (W.comp red) z) (Additive.ofMul (conj x)) = (z : Gamma0 N → Wc) (x : Gamma0 N)) ∧
      Function.Injective S ∧
      (∀ φ : CohCarrier.H1 (N * q ^ 2) H₁ Wc, φ ∈ LinearMap.range S ↔
        ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker),
          φ (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) = W (red γ) (φ (Additive.ofMul (conj ⟨y, hy⟩)))) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], Nat.Coprime ℓ (N * q) → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∃ T : HeckeEis.coeffH1 (W.comp red) →ₗ[K] HeckeEis.coeffH1 (W.comp red),
          HeckeEis.IsCoeffHeckeOnH1 N ℓ (W.comp red) (W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))) T ∧
          ∀ x : HeckeEis.coeffH1 (W.comp red),
            S (T x) = (W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))).toAddMonoidHom.comp
              (CohCarrier.heckeT (N * q ^ 2) H₁ ℓ Wc (S x)) := by sorry
