-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
-- name    : ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/3f14717d-4c88-5e04-8554-331881230e17
-- title:
--   Integrality of the geometric fibre charts of the Igusa scheme
-- statement:
--   Fix $N \ge 1$, a prime $\ell$ with $\ell \nmid N$, and an algebraically closed field $k$ carrying an algebra structure over the subring $\mathbb{Z}_{(\ell)} =$ [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$, namely the rationals whose denominator is coprime to $\ell$. Inside the field `modularFunctionFieldFull N`, write $j$ for the element `jFull N` given by the $q$-expansion `jq`, and for a subset $S$ let `chartAlg N ℓ S` be the $\mathbb{Z}_{(\ell)}$-subalgebra of elements integral over $\mathbb{Z}_{(\ell)}[S]$; thus `chartAlgFin N ℓ`, `chartAlgInf N ℓ` and `chartAlgMid N ℓ` are the integral closures of $\mathbb{Z}_{(\ell)}[j]$, $\mathbb{Z}_{(\ell)}[j^{-1}]$ and $\mathbb{Z}_{(\ell)}[j,j^{-1}]$ in that field. The conclusion is that $k \otimes_{\mathbb{Z}_{(\ell)}} \mathrm{chartAlgFin}$ and $k \otimes_{\mathbb{Z}_{(\ell)}} \mathrm{chartAlgInf}$ are integral domains (in particular nonzero), while for the overlap ring only nontriviality is asserted: $k \otimes_{\mathbb{Z}_{(\ell)}} \mathrm{chartAlgMid} \neq 0$.
--
--   This is the ring-theoretic form of the statement that, for $\ell \nmid N$, both affine charts of the geometric fibre of the Igusa model of $X_0(N)$ over $\mathbb{Z}_{(\ell)}$ (in characteristic $0$ or $\ell$) are integral and that the two charts meet. It is used in the study of the fibres and nodes of the Igusa scheme, for instance in the results on fibres of residue fields, on minimal primes of the chart at infinity and on points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open ModularCurve
open ModularCurve.IgusaScheme

noncomputable section
set_option autoImplicit false

theorem ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k] :
    IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)) ∧
      IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgMid N ℓ)) := by sorry
