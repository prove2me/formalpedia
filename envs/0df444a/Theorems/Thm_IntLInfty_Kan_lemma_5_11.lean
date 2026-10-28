-- Prove2me | Theorems.Thm_IntLInfty_Kan_lemma_5_11
-- name    : IntLInfty.Kan.lemma_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:47.676031+00:00
-- url     : https://prove2.me/theorems/b40b128b-f774-43a9-9420-2ad6e5e23ead
-- title:
--   Lemma 5.11, p. 17 — Ωⁿ(Δᵐ) → Ωⁿ(Λ^{m,j}) ×_{Ωⁿ⁺¹_closed(Λ^{m,j})} Ωⁿ⁺¹_closed(Δᵐ) is a surjective submersion
-- statement:
--   Fix $r \ge 1$, $n \ge 0$, $m \ge 1$ and $0 \le j \le m$, and write $\Lambda^{m,j} \subseteq \Delta^m$ for the geometric horn (the union of the facets other than the $j$-th). An $n$-form on $\Lambda^{m,j}$ is a compatible tuple $(\alpha_i)_{i \ne j}$ of $n$-forms on these facets. Let
--   $$P = \big\{(\alpha, \beta) \in \Omega^n(\Lambda^{m,j}) \times \Omega^{n+1}_{\mathrm{closed}}(\Delta^m) \;:\; d\alpha = \beta|_{\Lambda^{m,j}}\big\}$$
--   be the pullback of $\Omega^n(\Lambda^{m,j}) \xrightarrow{d} \Omega^{n+1}_{\mathrm{closed}}(\Lambda^{m,j}) \leftarrow \Omega^{n+1}_{\mathrm{closed}}(\Delta^m)$, where $d\alpha = \beta|_\Lambda$ means $d\alpha_i = d_i\beta$ for every $i \ne j$. Then $P$ is a split submanifold of the product, and the natural map
--   $$\Omega^n(\Delta^m) \longrightarrow P,\qquad \bar\alpha \longmapsto \big(\bar\alpha|_{\Lambda^{m,j}},\ d\bar\alpha\big)$$
--   is a surjective submersion.
--
--   In the proof of Theorem 5.10 this is the right vertical map of the pullback square (34), which gives the Kan fibration $\int\tau_{\le n-1}L \to \int\tau_{<n-1}L$.
--
--   Differences from the source:
--   - encoding: de Rham forms on the m-simplex Δᵐ; Ωⁿ_{Cʳ}(M) = {α of class Cʳ | dα of class Cʳ} with its Banach topology (Convention 5.1, p. 13) → forms are ExteriorAlgebra((ℝᵐ)∗)-valued functions on ℝᵐ, only their values on the corner simplex {t ≥ 0, ∑ t ≤ 1} matter; d uses derivatives within Δᵐ; Ωⁿ_{Cʳ}(Δᵐ) = CrForms r m n, the closed span of the jets (all partial derivatives of order ≤ r of the coefficients of α and of dα, restricted to Δᵐ, sup norms); reason: this jet norm is equivalent to the Cʳ norm on α and dα; the jet image of these forms is closed, so the closed span is the space itself; faces are pullbacks along the affine cofaces of (3)
--   - encoding: Ωⁿ(Λ^{m,j}), forms on the geometric horn, with d and the restriction β|_Λ taken there → compatible tuples in HornSet of the CrForms levels; dα = β|_Λ as dCr (αᵢ) = faceCl i β for every i ≠ j; reason: the convention of the proof of Lemma 5.7 (p. 15): a map from Λ[m, j] is a map on Λ^{m,j} of the given class on each face
--   - reading: “Let P be the pullback of …” (the paper uses P as an object of the category of Banach manifolds) → P as a subset of (∏_{i≠j} Ωⁿ(Δᵐ⁻¹)) × Ωⁿ⁺¹_closed(Δᵐ), asserted to be a C^∞ split submanifold; reason: the pullback exists in the category because Ωⁿ⁺¹_closed(Δᵐ) → Ωⁿ⁺¹_closed(Λ^{m,j}) is a surjective submersion (Lemma 5.9, Lemma 4.4); the statement makes this presupposition explicit
--   - encoding: submersion: every point has a neighbourhood U of its image and a section U → M through it (Definition 4.1, p. 11); covers of Banach manifolds are the surjective submersions (Corollary 4.5) → IsSurjSubmersionOn κ M N: κ maps M onto N and every x ∈ M has an open U ∋ κ x of the ambient space and a C^∞ map s on U with s (κ x) = x and s y ∈ M, κ (s y) = y for y ∈ U ∩ N; reason: for a split submanifold N, smooth maps on U ∩ N are exactly the restrictions of smooth maps on ambient open sets (locally)
-- source:
--   Henriques, Integrating L∞-algebras, arXiv:math/0603563v2, p. 17, Lemma 5.11

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

namespace IntLInfty.Kan

theorem lemma_5_11 (r : ℕ) (hr : 1 ≤ r) (n m : ℕ) (j : Fin (m + 2)) :
    let P : Set (({i : Fin (m + 2) // i ≠ j} → CrForms r m n) × CrClosed r (m + 1) (n + 1)) :=
      {p | p.1 ∈ HornSet (X := fun q => CrForms r q n) (fun q i => faceCr r q n i) m j ∧
        ∀ i, dCr r m n (p.1 i) = faceCl r m (n + 1) i.1 p.2}
    IsSplitSubmanifold P ∧
      IsSurjSubmersionOn
        (fun a : CrForms r (m + 1) n => ((fun i => faceCr r m n i.1 a), dCr r (m + 1) n a))
        Set.univ P := by sorry

end IntLInfty.Kan
