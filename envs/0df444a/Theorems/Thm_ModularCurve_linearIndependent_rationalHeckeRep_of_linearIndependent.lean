-- Prove2me | Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
-- name    : ModularCurve.linearIndependent_rationalHeckeRep_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/7180edb4-a5ac-53bf-a11c-3bfea2eac889
-- title:
--   ℚₚ-independence of Hecke operators on the rational Tate module
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime. Assume [`ModularCurve.HeckeInputsAll N`](def/ModularCurve_HeckeInputsAll.html#L8), i.e. that for every prime $\ell$ the data `HeckeInputsAlong` over $\overline{\mathbb{Q}}$ at level $N$ and prime $\ell$ exist (integrality of the two Hecke maps, principality of divisors on the level-$N\ell$ function field, finiteness, and the fundamental identity together with the norm formula), and assume [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25), i.e. that the endomorphisms $\mathrm{heckeOperatorBar}\,N\,\ell$ of $J:=\mathrm{JZero}\,N$ — the group $\mathrm{Pic}^0$ of the modular function field of level $N$ over $\overline{\mathbb{Q}}$ — commute pairwise. The Hecke algebra is $\mathbb{T}=\mathbb{Z}[X_\ell : \ell \text{ prime}]$, acting on $J$ through [`ModularCurve.heckeModuleBar N`](def/ModularCurve_HeckeModule.html#L82), which under `hcomm` sends $X_\ell$ to $\mathrm{heckeOperatorBar}\,N\,\ell$. Let $\iota$ be a type and $t : \iota \to \mathbb{T}$ a family, and suppose the images of the $t_i$ in $\mathbb{T}/\mathrm{Ann}_{\mathbb{T}}(J)$ are $\mathbb{Z}$-linearly independent. Then the family of endomorphisms $\mathrm{rationalHeckeRep}\,p\,J\,(t_i)$ of the rational Tate module $\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J$ — the base change to $\mathbb{Q}_p$ of the action of $\mathbb{T}$ on $T_pJ$, where $T_pJ$ consists of sequences $(x_n)$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — is $\mathbb{Q}_p$-linearly independent in $\mathrm{End}_{\mathbb{Q}_p}(\mathbb{Q}_p \otimes_{\mathbb{Z}_p} T_p J)$.
--
--   This is the injectivity half of Tate's theorem $\mathrm{End}(B)\otimes\mathbb{Z}_p \hookrightarrow \mathrm{End}_{\mathbb{Z}_p}(T_pB)$ for $B = J_0(N)$, restricted to the Hecke subring and tensored with $\mathbb{Q}$: it says that $\mathbb{Q}_p\otimes_{\mathbb{Z}}\bigl(\mathbb{T}/\mathrm{Ann}_{\mathbb{T}}(J)\bigr)$ maps injectively into $\mathrm{End}_{\mathbb{Q}_p}(V_pJ_0(N))$. It is used to transport eigencharacters of the geometric Hecke quotient to characters of the image algebra inside $\mathrm{End}_{\mathbb{Q}_p}(V_p)$, and so feeds the construction of the $p$-adic representation attached to a normalised eigenform and the comparison of Hecke lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.linearIndependent_rationalHeckeRep_of_linearIndependent (N p : ℕ) [NeZero N]
    [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {ι : Type} (t : ι → ModularCurve.HeckeAlg)
    (hli : letI := ModularCurve.heckeModuleBar N
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N)) (t i))) :
    letI := ModularCurve.heckeModuleBar N
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (t i)) := by sorry
