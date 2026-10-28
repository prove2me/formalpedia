-- Prove2me | Theorems.Thm_IntLInfty_Kan_lemma_5_9
-- name    : IntLInfty.Kan.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:51.690979+00:00
-- url     : https://prove2.me/theorems/4effe2c4-5be5-4092-8915-2eed3144b00c
-- title:
--   Lemma 5.9, p. 15 — the simplicial Banach spaces Ωⁿ(Δ•) and Ωⁿ_closed(Δ•) satisfy the Kan condition
-- statement:
--   Fix $r \ge 1$ and $n \ge 0$. The simplicial Banach space $X$ with $X_m = \Omega^n_{C^r}(\Delta^m)$ and face maps the pullbacks along the cofaces satisfies the Kan condition: for all $m \ge 1$ and $0 \le j \le m$, the space $\mathrm{Hom}(\Lambda[m,j], X)$ of compatible tuples of $n$-forms on the facets of $\Delta^m$ other than the $j$-th is a split submanifold of $\prod_{i \ne j}\Omega^n(\Delta^{m-1})$, and the restriction map
--   $$\Omega^n(\Delta^m) \longrightarrow \mathrm{Hom}(\Lambda[m,j], X)$$
--   is a surjective submersion. The same holds for $X_m = \Omega^n_{\mathrm{closed}}(\Delta^m)$.
--
--   Together with Lemma 2.7 this gives the Kan fibration $\int\tau_{<n}L \to \int\tau_{\le n-1}L$ in the proof of Theorem 5.10.
--
--   Differences from the source:
--   - encoding: de Rham forms on the m-simplex Δᵐ; Ωⁿ_{Cʳ}(M) = {α of class Cʳ | dα of class Cʳ} with its Banach topology (Convention 5.1, p. 13) → forms are ExteriorAlgebra((ℝᵐ)∗)-valued functions on ℝᵐ, only their values on the corner simplex {t ≥ 0, ∑ t ≤ 1} matter; d uses derivatives within Δᵐ; Ωⁿ_{Cʳ}(Δᵐ) = CrForms r m n, the closed span of the jets (all partial derivatives of order ≤ r of the coefficients of α and of dα, restricted to Δᵐ, sup norms); reason: this jet norm is equivalent to the Cʳ norm on α and dα; the jet image of these forms is closed, so the closed span is the space itself; faces are pullbacks along the affine cofaces of (3)
--   - encoding: “X is Kan” for the simplicial manifolds Xₘ = Ωⁿ(Δᵐ), Ωⁿ_closed(Δᵐ) → SatisfiesKan for the levels CrForms r m n, resp. CrClosed r m n, with faces faceCr, faceCl: for all m ≥ 1, j, the horn set (compatible tuples) is a split submanifold and the restriction map is a surjective submersion from the whole space; reason: X is not reduced for n = 0, so “Kan” is the Kan condition of Definition 1.2; its levels are Banach spaces, so they are manifolds
--   - encoding: submersion: every point has a neighbourhood U of its image and a section U → M through it (Definition 4.1, p. 11); covers of Banach manifolds are the surjective submersions (Corollary 4.5) → IsSurjSubmersionOn κ M N: κ maps M onto N and every x ∈ M has an open U ∋ κ x of the ambient space and a C^∞ map s on U with s (κ x) = x and s y ∈ M, κ (s y) = y for y ∈ U ∩ N; reason: for a split submanifold N, smooth maps on U ∩ N are exactly the restrictions of smooth maps on ambient open sets (locally)
-- source:
--   Henriques, Integrating L∞-algebras, arXiv:math/0603563v2, p. 15, Lemma 5.9

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

namespace IntLInfty.Kan

theorem lemma_5_9 (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    SatisfiesKan (fun m => CrForms r m n) (fun m i => faceCr r m n i) ∧
    SatisfiesKan (fun m => CrClosed r m n) (fun m i => faceCl r m n i) := by sorry

end IntLInfty.Kan
