-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_lemma_2_2
-- name    : MomentPolytopes.QuantumFunctionals.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:03:21.158116+00:00
-- url     : https://prove2.me/theorems/8ecf8317-8e50-49f6-8a0a-4f076855a781
-- title:
--   Lemma 2.2 — a geodesic ray g†e^{tX}g on P is asymptotic to t ↦ e^{t u†Xu} for some u ∈ K
-- statement:
--   Let $G\subseteq\mathrm{GL}(n)$ be a connected, Zariski-closed, self-adjoint subgroup, $K=G\cap\mathrm U(n)$ and $H=\operatorname{Lie}G\cap\mathrm{Herm}(n)$. For every $g\in G$ and $X\in H$ there is $u\in K$ such that the geodesic rays $t\mapsto g^\dagger e^{tX}g$ and $t\mapsto e^{t\,u^\dagger Xu}$ on $P=G\cap\mathrm{PD}(n)$ are asymptotic: there is $B$ with
--   $$d\big(g^\dagger e^{tX}g,\ e^{t\,u^\dagger Xu}\big)\le B\qquad\text{for all }t\ge0,$$
--   where $d(x,y)=\|\log(x^{-1/2}yx^{-1/2})\|_F$ is the affine-invariant distance.
--
--   The proof of Theorem 6.28 uses this lemma to compare Busemann functions before and after acting by an integer matrix tuple $g$.
--
--   Differences from the source:
--   - encoding: asymptotic: d(γ(t), β(t)) remains bounded as t → ∞ → ∃ B, ∀ t ≥ 0, pdDist (γ t) (β t) ≤ B; reason: both rays are continuous on [0, ∞), so boundedness as t → ∞ and on [0, ∞) agree
--   - encoding: connected Zariski-closed self-adjoint subgroup; H = Lie G ∩ Herm(n) → IsConnSelfAdjointAlgGroup (subgroup, zero set in GL(n) of a polynomial family, closed under †, Euclidean-connected); groupH = {X Hermitian | e^{tX} ∈ G ∀ t}; reason: equivalent definitions; Zariski- and Euclidean-connectedness agree for complex algebraic groups
--   - generalization: G ⊆ GL(n) with n ≥ 1 → any n : ℕ, including n = 0; reason: n = 0 is the trivial group, where the claim is immediate; at n ≥ 1 the statement is the source's
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 16, Lemma 2.2 (proof in App. B, p. 69)

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_SelfAdjointGroup

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Lemma 2.2 (p. 16; proof in App. B, p. 69). Let `G ⊆ GL(n)` be a connected, Zariski-closed,
self-adjoint subgroup with `K = G ∩ U(n)` and `H = Lie G ∩ Herm(n)`. For `g ∈ G` and `X ∈ H`,
the geodesic ray `t ↦ g† e^{tX} g` on `P` is asymptotic to `t ↦ e^{t u†Xu}` for some `u ∈ K`:
their affine-invariant distance stays bounded for `t ≥ 0`. -/
theorem lemma_2_2 (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (hG : IsConnSelfAdjointAlgGroup G) (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ G)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ groupH G) :
    ∃ u ∈ groupK G, ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      pdDist (gᴴ * hermExp t X * g) (hermExp t (uᴴ * X * u)) ≤ B := by sorry

end MomentPolytopes.QuantumFunctionals
