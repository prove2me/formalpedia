-- Prove2me | Theorems.Thm_ModularCurve_heckeAlg_smul_comm_of_forall_gen
-- name    : ModularCurve.heckeAlg_smul_comm_of_forall_gen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/3230bb31-6272-5f75-8414-a0edd300b0ee
-- title:
--   Additive maps commuting with all T_ℓ are T-linear
-- statement:
--   Here $\mathbb{T}$ denotes the abstract Hecke algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14), which is by definition the polynomial ring $\mathbb{Z}[X_\ell : \ell \in \mathrm{Primes}]$ on one indeterminate for each prime (formally `MvPolynomial Nat.Primes ℤ`), and for a prime $q$ the element [`ModularCurve.heckeGen q`](def/HeckeGalois_EichlerShimura.html#L16) is the indeterminate $X_q$ attached to $q$. Let $J$ and $J'$ be additive commutative groups, each carrying a module structure over $\mathbb{T}$, and let $\mathrm{sp} : J \to J'$ be a homomorphism of additive groups. Assume that $\mathrm{sp}$ is equivariant for each of the generators: for every prime $q$ and every $x \in J$ one has $\mathrm{sp}(X_q \cdot x) = X_q \cdot \mathrm{sp}(x)$. The conclusion is that $\mathrm{sp}$ is equivariant for the whole algebra: for every $T \in \mathbb{T}$ and every $x \in J$, $\mathrm{sp}(T \cdot x) = T \cdot \mathrm{sp}(x)$; that is, the additive map $\mathrm{sp}$ is $\mathbb{T}$-linear.
--
--   This is the extension-from-generators principle for maps of Hecke modules: equivariance checked on the generators $T_\ell$, which is what geometric correspondences supply, is upgraded to linearity over the full Hecke algebra. It is used in the construction of Néron-model data for Jacobians of modular curves and in deducing that the relevant Hecke operators act with commuting scalar actions on $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeAlg_smul_comm_of_forall_gen.lean

import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeAlg_smul_comm_of_forall_gen {J J' : Type*} [AddCommGroup J] [AddCommGroup J'] [Module ModularCurve.HeckeAlg J] [Module ModularCurve.HeckeAlg J'] (sp : J →+ J') (hgen : ∀ (q : Nat.Primes) (x : J), sp (ModularCurve.heckeGen q • x) = ModularCurve.heckeGen q • sp x) (T : ModularCurve.HeckeAlg) (x : J) : sp (T • x) = T • sp x := by sorry
