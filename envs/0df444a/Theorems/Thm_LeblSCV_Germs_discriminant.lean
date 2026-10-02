-- Prove2me | Theorems.Thm_LeblSCV_Germs_discriminant
-- name    : LeblSCV.Germs.discriminant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:56.980196+00:00
-- url     : https://prove2.me/theorems/9ae06d9a-9c0d-4410-9543-04841297b1c3
-- title:
--   Theorem 6.3.3 — the discriminant function
-- statement:
--   Let $D \subset \mathbb{C}$ be a bounded domain, $U' \subset \mathbb{C}^{n-1}$ a domain, and $f \in \mathcal{O}(U' \times D)$. Suppose the zero set $f^{-1}(0) \subset U' \times D$ has no limit points on $U' \times \partial D$. Then there exist an integer $m \ge 0$ and a holomorphic function $\Delta : U' \to \mathbb{C}$, not identically zero, such that, with $E = \Delta^{-1}(0)$,
--   $$ \#\{ w \in D : f(z', w) = 0 \} = m \quad (z' \in U' \setminus E), \qquad \#\{ w \in D : f(z', w) = 0 \} < m \quad (z' \in E). $$
--   Zeros are counted **geometrically**, i.e. as distinct points, without multiplicity.
--
--   $\Delta$ is the discriminant function and $E$ the discriminant set: away from a thin set the zeros of $z_n \mapsto f(z', z_n)$ stay distinct, and they come together only over the zero set of a single holomorphic function.
--
--   **Formalization Note.** $\mathbb{C}^{n-1}$ is `Fin d → ℂ`; domains are `IsOpen ∧ IsConnected`; bounded is `Bornology.IsBounded`; $\partial D$ is `frontier D`. "No limit points on $U' \times \partial D$" is: no point of $U' \times \partial D$ lies in the closure of $\{w \in U' \times D : f(w) = 0\}$ (such points are outside $U' \times D$, so limit point and closure point agree). Counts use `Set.encard` (values in `ℕ∞`), so an infinite zero set is never counted as $0$. The book writes $m \in \mathbb{N}$ with $\mathbb{N} = \{1, 2, \dots\}$; the statement allows $m = 0$, because for $f$ without zeros (e.g. $f \equiv 1$) the hypotheses hold and only $m = 0$ satisfies the conclusion. The book's proof takes $m$ to be the maximal number of distinct zeros, which is $0$ in that case.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 178, Theorem 6.3.3

import Mathlib

namespace LeblSCV.Germs

/-- Theorem 6.3.3 (Lebl, p. 178). `ℂ^{n-1}` is `Fin d → ℂ` with `d = n - 1`. Let `D ⊆ ℂ` be a
bounded domain, `U' ⊆ ℂ^{n-1}` a domain and `f ∈ 𝒪(U' × D)`. Suppose the zero set
`f⁻¹(0) ⊆ U' × D` has no limit points on `U' × ∂D`. Then there are `m` and a holomorphic
`Δ : U' → ℂ`, not identically zero, such that for every `z' ∈ U' ∖ E`, `E = Δ⁻¹(0)`, the function
`z_n ↦ f(z', z_n)` has exactly `m` geometrically distinct zeros in `D`, and strictly fewer than
`m` for `z' ∈ E`. Zeros are counted without multiplicity (`Set.encard` of the zero set in `D`,
which also rules out an infinite zero set). The book writes `m ∈ ℕ` (`ℕ = {1, 2, …}`), but for
`f` without zeros only `m = 0` is possible; the statement here allows `m = 0` (see the
moderation notes). -/
theorem discriminant {d : ℕ} (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D)
    (hDb : Bornology.IsBounded D) (U' : Set (Fin d → ℂ)) (hU'o : IsOpen U')
    (hU'c : IsConnected U') (f : (Fin d → ℂ) × ℂ → ℂ) (hf : DifferentiableOn ℂ f (U' ×ˢ D))
    (hlim : ∀ z ∈ U' ×ˢ frontier D, z ∉ closure {w | w ∈ U' ×ˢ D ∧ f w = 0}) :
    ∃ (m : ℕ) (Δ : (Fin d → ℂ) → ℂ), DifferentiableOn ℂ Δ U' ∧ (∃ z' ∈ U', Δ z' ≠ 0) ∧
      (∀ z' ∈ U', Δ z' ≠ 0 → {w : ℂ | w ∈ D ∧ f (z', w) = 0}.encard = (m : ℕ∞)) ∧
      (∀ z' ∈ U', Δ z' = 0 → {w : ℂ | w ∈ D ∧ f (z', w) = 0}.encard < (m : ℕ∞)) := by sorry

end LeblSCV.Germs
