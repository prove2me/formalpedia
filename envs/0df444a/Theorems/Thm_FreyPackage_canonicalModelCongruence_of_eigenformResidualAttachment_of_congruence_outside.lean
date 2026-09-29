-- Prove2me | Theorems.Thm_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside
-- name    : FreyPackage.canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/02bafab5-7ba5-5d30-b923-0a31b9ff857f
-- title:
--   Transfer of the Frey congruence to the canonical integral model
-- statement:
--   Let $P$ be a Frey package (nonzero integers $a,b,c$ with $a^p+b^p=c^p$, $p$ prime, $p\ge 5$, $\gcd(a,b)=1$, $a\equiv 3 \bmod 4$, $b\equiv 0\bmod 2$). Assume `hatt`: for every $M>0$ the project's predicate `P.EigenformResidualAttachmentAt M` holds, i.e. for every normalised weight-$2$ eigenform $g$ on $\Gamma_0(M)$ (normalised in the project's sense: $a_1(g)=1$ together with the multiplicativity and Hecke recursions on $q$-coefficients) and every maximal ideal $\mathfrak m$ of $\overline{\mathbb Z}=$ `integralClosure ℤ ℂ` containing $p$, there are a field $K$ which is a $\mathbb Z/p$-algebra, a two-dimensional $K$-space $V$ with a representation $\rho$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, a ring map $\psi:\overline{\mathbb Z}\to K$ with $\mathfrak m\subseteq\ker\psi$, and a finite Galois $F/\mathbb Q$ inside $\overline{\mathbb Q}$ whose associated restriction kernel kills both $\rho$ and the mod-$p$ Frey representation `galoisRepModuleEnd ℚ P.freyCurve P.p`, such that at every Frobenius $\tau$ at a prime $\ell\nmid M$, $\ell\ne p$ (relative to a valuation subring over $\ell$) one has $\mathrm{tr}\,\rho(\tau)=\psi(a)$ for some $a\in\overline{\mathbb Z}$ with $a=a_\ell(g)$ in $\mathbb C$, and $\det\rho(\tau)=\ell$. Let $f$ be a normalised weight-$2$ eigenform on $\Gamma_0(M)$, let $W$ be an integral Weierstrass model of `P.freyCurve` (a rational variable change carries the Frey curve to $W$ over $\mathbb Q$), let $\mathfrak m$ be maximal with $p\in\mathfrak m$, and let $S_0$ be a finite set of naturals. Assume that for every prime $\ell\notin S_0$ with $\ell\nmid\Delta(W)$ (the project's `IsGoodPrimeFor`, i.e. $\ell$ does not divide the discriminant of that model), $\ell\nmid M$ and $\ell\ne p$, there is $a\in\overline{\mathbb Z}$ with $a=a_\ell(f)$ in $\mathbb C$ and $a-a_\ell(W)\in\mathfrak m$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ mod $\ell$. The conclusion: for every prime $\ell_0$ with $\ell_0\nmid\Delta(\texttt{freyCurveInt}\,P)$, $\ell_0\nmid M$ and $\ell_0\ne p$ — with no condition involving $S_0$ or $W$ — there is $a\in\overline{\mathbb Z}$ with $a=a_{\ell_0}(f)$ in $\mathbb C$ and $a-a_{\ell_0}(\texttt{freyCurveInt}\,P)\in\mathfrak m$.
--
--   This is the propagation step underlying the comparison of a mod-$\mathfrak m$ eigenform representation with the mod-$p$ representation on the $p$-torsion of the Frey curve, as in Ribet's work on modular representations and in Darmon–Diamond–Taylor; here it appears in the shape needed to move a congruence known only outside a finite set $S_0$ and only at primes not dividing the discriminant of an arbitrary integral model $W$ to a congruence at every prime not dividing the discriminant of the project's canonical model `freyCurveInt`. The modularity input is not proved but assumed, as the project's `EigenformResidualAttachmentAt` at every positive level; note also that 'good prime' here means only non-divisibility of the discriminant of the chosen Weierstrass model, not good reduction of the curve. It is used in the level-lowering statement [`FreyPackage.level_lowering_odd_prime_of_conductorLevel`](thm.html#FreyPackage.level_lowering_odd_prime_of_conductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside.lean

import Mathlib
import Definitions.Def_FreyPackage_RouteAReversePinSeam
import Definitions.Def_FreyPackage_EigenformResidualAttachment

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.canonicalModelCongruence_of_eigenformResidualAttachment_of_congruence_outside (P : FreyPackage)
    (hatt : ∀ M : ℕ, 0 < M → P.EigenformResidualAttachmentAt M)
    {M : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve)
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (P.p : integralClosure ℤ ℂ) ∈ 𝔪)
    (S₀ : Finset ℕ)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∀ ℓ₀ : ℕ, ℓ₀.Prime → (FreyPackage.freyCurveInt P).IsGoodPrimeFor ℓ₀ → ¬ ℓ₀ ∣ M → ℓ₀ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ₀ ∧
        a - (((FreyPackage.freyCurveInt P).apOfModel ℓ₀ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪 := by sorry
