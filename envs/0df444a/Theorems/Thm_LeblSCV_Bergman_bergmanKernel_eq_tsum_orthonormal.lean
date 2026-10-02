-- Prove2me | Theorems.Thm_LeblSCV_Bergman_bergmanKernel_eq_tsum_orthonormal
-- name    : LeblSCV.Bergman.bergmanKernel_eq_tsum_orthonormal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:01.546315+00:00
-- url     : https://prove2.me/theorems/3e3d30a4-5783-4b39-846a-0e418b1c5e75
-- title:
--   Proposition 5.2.5 — the Bergman kernel as a sum over a complete orthonormal system
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and $\{\varphi_\ell\}_{\ell \in I}$ a complete orthonormal system for $A^2(U)$, with $I$ an arbitrary index set. Then
--   $$K_U(z, \bar\zeta) = \sum_{\ell \in I} \varphi_\ell(z) \, \overline{\varphi_\ell(\zeta)},$$
--   with uniform convergence on compact subsets of $U \times U^*$, where $U^* = \{\zeta : \bar\zeta \in U\}$. Explicitly: for every compact $L \subset U \times U$ of pairs $(z, \zeta)$ and every $\varepsilon > 0$ there is a finite $F \subset I$ such that
--   $$\Big| K_U(z, \bar\zeta) - \sum_{\ell \in s} \varphi_\ell(z)\overline{\varphi_\ell(\zeta)} \Big| < \varepsilon \quad \text{for all finite } s \supseteq F \text{ and all } (z, \zeta) \in L.$$
--
--   Although the Bergman kernel can rarely be computed in closed form, this expansion computes it from any orthonormal basis of $A^2(U)$ (for the ball, from the normalized monomials), and shows it is a locally uniform limit of explicit holomorphic-antiholomorphic sums.
--
--   **Formalization Note.** `bergmanKernel U z ζ` is $K_U(z, \bar\zeta)$; the map $(z, \bar\zeta) \mapsto (z, \zeta)$ is a homeomorphism of $U \times U^*$ onto $U \times U$, so compact subsets of $U \times U^*$ correspond to compact subsets `L ⊆ U ×ˢ U`. $\varphi_\ell(z)$ is `holoRep U (φ ℓ) z`. The sum over $I$ is unordered: the finite partial sums, indexed by `Finset I` with the filter `atTop`, converge uniformly on $L$ (`TendstoUniformlyOn`). For countable $I$ this implies uniform convergence of the partial sums in any enumeration.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 163, Proposition 5.2.5

import Mathlib
import Definitions.Def_LeblSCV_Bergman_IsCompleteOrthonormalSystem
import Definitions.Def_LeblSCV_Bergman_bergmanKernel

open MeasureTheory Filter

namespace LeblSCV.Bergman

/-- Lebl, Proposition 5.2.5 (p. 163). Suppose `U ⊆ ℂⁿ` is a domain and `{φ_ℓ}_{ℓ ∈ I}` is a
complete orthonormal system for `A²(U)`. Then `K_U(z, ζ̄) = ∑_{ℓ ∈ I} φ_ℓ(z) \overline{φ_ℓ(ζ)}`,
with uniform convergence on compact subsets of `U × U*`.
Here `bergmanKernel U z ζ` is `K_U(z, ζ̄)`, so the book's `(z, ζ̄) ∈ U × U*` is `(z, ζ) ∈ U × U`;
the sum over the arbitrary index set `I` is the limit of the finite partial sums along the
directed set of finite subsets of `I`, uniformly on every compact `L ⊆ U × U`. -/
theorem bergmanKernel_eq_tsum_orthonormal {n : ℕ} {U : Set (Fin n → ℂ)} (hU_open : IsOpen U)
    (hU_conn : IsConnected U) {I : Type*} (φ : I → bergmanSpace U)
    (hφ : IsCompleteOrthonormalSystem U φ) (L : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (hL : IsCompact L) (hLU : L ⊆ U ×ˢ U) :
    TendstoUniformlyOn
      (fun (s : Finset I) (p : (Fin n → ℂ) × (Fin n → ℂ)) =>
        ∑ ℓ ∈ s, holoRep U (φ ℓ) p.1 * (starRingEnd ℂ) (holoRep U (φ ℓ) p.2))
      (fun p => bergmanKernel U p.1 p.2) atTop L := by sorry

end LeblSCV.Bergman
