-- Prove2me | Theorems.Thm_InfiniteGalois_nonempty_continuousMulEquiv_fixedField_ker
-- name    : InfiniteGalois.nonempty_continuousMulEquiv_fixedField_ker
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:23:51.728815+00:00
-- url     : https://prove2.me/theorems/fb4c7e33-3f29-4ce5-8e1c-3df842fec2dd
-- title:
--   A continuous surjection of a Galois group onto a Hausdorff group is realised by the fixed field of its kernel
-- statement:
--   Let $K/k$ be a (possibly infinite) Galois extension with Galois group $G=\mathrm{Gal}(K/k)$, equipped with the Krull topology. Let $\Gamma$ be a Hausdorff topological group and let
--   $$\varphi : G\longrightarrow\Gamma$$
--   be a continuous surjective group homomorphism. Let $L=K^{\ker\varphi}$ be the fixed field of its kernel. Then $L/k$ is Galois and
--   $$\mathrm{Gal}(L/k)\;\cong\;\Gamma$$
--   as topological groups.
--
--   This is the topological form of the fundamental theorem of infinite Galois theory for quotients: $\ker\varphi$ is a closed normal subgroup, $\mathrm{Gal}(L/k)\cong G/\ker\varphi$, and the latter is homeomorphic to $\Gamma$ because $G$ is compact. It is the standard way to produce extensions with prescribed profinite Galois group, e.g. $\mathbb Z_p$-extensions from a continuous surjection $G\to\mathbb Z_p$.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Chapter IV, §1, Theorem (1.4) (fundamental theorem of infinite Galois theory: G(K|k)/G(K|Ω) ≅ G(Ω|k) for closed normal subgroups); cf. Mathlib InfiniteGalois.normalAutEquivQuotient.

import Mathlib.FieldTheory.Galois.Infinite

open IntermediateField

theorem InfiniteGalois.nonempty_continuousMulEquiv_fixedField_ker {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    (φ : Gal(K/k) →* Γ) (hφ : Continuous φ) (hs : Function.Surjective φ) :
    IsGalois k (fixedField φ.ker) ∧ Nonempty (Gal(fixedField φ.ker/k) ≃ₜ* Γ) := by sorry
