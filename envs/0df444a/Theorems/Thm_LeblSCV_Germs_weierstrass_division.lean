-- Prove2me | Theorems.Thm_LeblSCV_Germs_weierstrass_division
-- name    : LeblSCV.Germs.weierstrass_division
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:23.297241+00:00
-- url     : https://prove2.me/theorems/768d4a04-0689-4a5f-ab06-8ed2b4ace614
-- title:
--   Theorem 6.2.5 — Weierstrass division theorem
-- statement:
--   Let $f$ be holomorphic near the origin of $\mathbb{C}^{n-1} \times \mathbb{C}$, and let $P(z', z_n) = z_n^k + \sum_{\ell=0}^{k-1} c_\ell(z') z_n^\ell$ be a Weierstrass polynomial of degree $k \ge 1$ in $z_n$. Then there exist a neighborhood $V$ of the origin and $q, r \in \mathcal{O}(V)$, where $r$ is a polynomial in $z_n$ of degree less than $k$ whose coefficients are holomorphic functions of $z'$,
--   $$ r(z', z_n) = \sum_{\ell=0}^{k-1} b_\ell(z')\, z_n^\ell, $$
--   such that on $V$
--   $$ f = qP + r, $$
--   and $q$ and $r$ are unique with these properties.
--
--   This generalizes division with remainder by a monic polynomial to the case where the dividend $f$ is an arbitrary holomorphic function, a "polynomial of infinite degree". The remainder need not be monic and its coefficients need not vanish at the origin.
--
--   **Formalization Note.** $\mathbb{C}^{n-1} \times \mathbb{C}$ is `(Fin d → ℂ) × ℂ`. "Holomorphic near the origin" is `DifferentiableOn ℂ f W` for an open $W \ni 0$; $P$ is `IsWeierstrassPolynomial U' c` for an open $U' \ni 0$. The neighborhood $V$ is open, contained in $W$ and in $U' \times \mathbb{C}$ (where $f$ and $P$ are defined). The coefficients $b_\ell$ of $r$ are holomorphic on the projection of $V$ to $\mathbb{C}^{n-1}$. Uniqueness: any $q_2, r_2$ holomorphic on $V$, with $r_2$ of the same polynomial form and $f = q_2 P + r_2$ on $V$, agree with $q, r$ on $V$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 175, Theorem 6.2.5

import Mathlib
import Definitions.Def_LeblSCV_Germs_weierstrassPolynomial

namespace LeblSCV.Germs

/-- Theorem 6.2.5 (Weierstrass division theorem, Lebl, p. 175). `ℂ^{n-1} × ℂ` is
`(Fin d → ℂ) × ℂ` with `d = n - 1`. Let `f` be holomorphic on an open neighborhood `W` of the
origin and `P` a Weierstrass polynomial of degree `k ≥ 1` in `z_n` with coefficients `c_ℓ`
holomorphic on `U' ∋ 0`. Then there is an open neighborhood `V ⊆ W ∩ (U' × ℂ)` of the origin
and `q, r ∈ 𝒪(V)`, where `r(z', z_n) = ∑_{ℓ<k} b_ℓ(z') z_nˡ` is a polynomial in `z_n` of degree
less than `k` whose coefficients are holomorphic functions of `z'`, with `f = qP + r` on `V`;
and `q`, `r` are unique on `V` with these properties. -/
theorem weierstrass_division {d k : ℕ} (hk : 1 ≤ k) (W : Set ((Fin d → ℂ) × ℂ))
    (hW : IsOpen W) (h0W : (0 : (Fin d → ℂ) × ℂ) ∈ W) (f : (Fin d → ℂ) × ℂ → ℂ)
    (hf : DifferentiableOn ℂ f W) (U' : Set (Fin d → ℂ)) (c : Fin k → (Fin d → ℂ) → ℂ)
    (hP : IsWeierstrassPolynomial U' c) :
    ∃ V : Set ((Fin d → ℂ) × ℂ), IsOpen V ∧ (0 : (Fin d → ℂ) × ℂ) ∈ V ∧ V ⊆ W ∧
      V ⊆ U' ×ˢ Set.univ ∧
      ∃ q r : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ q V ∧ DifferentiableOn ℂ r V ∧
        (∃ b : Fin k → (Fin d → ℂ) → ℂ, (∀ ℓ, DifferentiableOn ℂ (b ℓ) (Prod.fst '' V)) ∧
          ∀ z ∈ V, r z = ∑ ℓ : Fin k, b ℓ z.1 * z.2 ^ (ℓ : ℕ)) ∧
        (∀ z ∈ V, f z = q z * weierstrassPolyFun c z + r z) ∧
        ∀ q₂ r₂ : (Fin d → ℂ) × ℂ → ℂ,
          DifferentiableOn ℂ q₂ V → DifferentiableOn ℂ r₂ V →
          (∃ b : Fin k → (Fin d → ℂ) → ℂ, (∀ ℓ, DifferentiableOn ℂ (b ℓ) (Prod.fst '' V)) ∧
            ∀ z ∈ V, r₂ z = ∑ ℓ : Fin k, b ℓ z.1 * z.2 ^ (ℓ : ℕ)) →
          (∀ z ∈ V, f z = q₂ z * weierstrassPolyFun c z + r₂ z) →
          Set.EqOn q₂ q V ∧ Set.EqOn r₂ r V := by sorry

end LeblSCV.Germs
