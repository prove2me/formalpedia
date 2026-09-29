-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/63ae4e34-9144-5054-b8de-b51a7600f8c2
-- title:
--   Sequential compactness of the ℂ-points of an abelian scheme
-- statement:
--   Let $G$ be a scheme and $f : G \to \operatorname{Spec}\mathbb{C}$ a morphism, equipped with a relative group law $L$ in the sense of `RelativeGroupLaw`: for every scheme $T$ and every $t : T \to \operatorname{Spec}\mathbb{C}$ the set of $T$-points over $t$ (morphisms $T \to G$ whose composite with $f$ is $t$) carries operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ satisfying associativity, the two unit laws and left inverses, with $\mathrm{mul}$ natural in $T$. Assume `AbelianSchemePropertyBundle ℂ f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law; assume moreover that for every point $s$ of $\operatorname{Spec}\mathbb{C}$ the fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $P : \mathbb{N} \to \{\varphi : \operatorname{Spec}\mathbb{C} \to G \mid \varphi \circ\text{-}\mathrm{then}\text{-}f = \mathrm{id}\}$ be a sequence of $\mathbb{C}$-points. Then there exist a $\mathbb{C}$-point $Q$ and a strictly monotone $\varphi : \mathbb{N} \to \mathbb{N}$ such that for every affine open $U \subseteq G$ through which $Q$ factors (i.e. $\top \le Q^{-1}U$) there is $n_0$ with: $P(\varphi(n))$ factors through $U$ for all $n \ge n_0$, and for every $s \in \Gamma(G,U)$ the sequence of complex numbers $s(P(\varphi(n)))$, read off through `appLE U ⊤` and `Scheme.ΓSpecIso`, and set to $0$ for $n < n_0$, tends to $s(Q)$ as $n \to \infty$.
--
--   This is the statement that the $\mathbb{C}$-points of an abelian scheme over $\mathbb{C}$ are sequentially compact for the topology in which a point is approached when the values of all sections on an affine neighbourhood converge; its conclusion has the same shape as the corresponding statement for proper smooth relative curves. It feeds the construction of the analytic quotient description of the points, being cited by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology
open AlgebraicGeometry

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_tendsto_appLE_complex
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
    (hA : AbelianSchemePropertyBundle ℂ f) {g : ℕ}
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :
    ∃ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (U : G.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P (φ n)).1 ⁻¹ᵁ U,
          ∀ s : Γ(G, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P (φ n)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hQ) s))) := by sorry
