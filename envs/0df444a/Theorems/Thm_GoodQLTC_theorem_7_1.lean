-- Prove2me | Theorems.Thm_GoodQLTC_theorem_7_1
-- name    : GoodQLTC.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:09.295475+00:00
-- url     : https://prove2.me/theorems/174c5c57-14ec-4345-a6f3-1a6b741c2e0c
-- title:
--   Theorem 7.1: mixing of cubical face walks
-- statement:
--   Let $\tau\ge1$ and $X$ a regular, $\lambda$-expanding $t$-dimensional cubical complex, $t\ge2$, with degrees $2\le n_1\le\dots\le n_t$ and $n_t/n_1\le\tau$; $Z_j=|X(j)|$. There is a constant $C_{\mathrm{mix}}=C_{\mathrm{mix}}(t,\tau)>0$ such that for every $1\le j<t$ and $0\le\ell\le j$ the walk $W_{j\ell}$ is reversible for the uniform measure on $X(j)$, and every $B\subseteq X(j)$ satisfies
--   $$
--   \langle 1_B,W_{j\ell}1_B\rangle\le\lambda|B|+C_{\mathrm{mix}}\frac{|B|^2}{Z_j}.
--   $$
--   The constant is the explicit one chosen in the proof (p.24).
--
--   Differences from the source:
--   - generalization: there is a constant C_mix(t, τ) > 0 → the explicit C_mix(t, τ) of the proof (maximum of binom(t,p) 2^{t−p−1} τ^q over 1 ≤ q < t, 0 ≤ p ≤ q), asserted positive; reason: the explicit constant witnesses the existential; Theorem 8.2 uses this value by name
--   - encoding: reversible for the uniform measure → W_{jℓ}(f, g) = W_{jℓ}(g, f) for f, g ∈ X(j); reason: reversibility for a uniform measure is symmetry of the kernel
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 7.1, p.24 (PDF p.27); walk and (7.1), p.23; C_mix in its proof, p.24

import Mathlib
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_faceWalk

namespace GoodQLTC

/-- **Theorem 7.1** (mixing of cubical face walks), Gay–Jeronimo, arXiv:2609.20780 (held version),
p.24: there is a constant `C_mix = C_mix(t, τ) > 0` such that, for every `1 ≤ j < t` and
`0 ≤ ℓ ≤ j`, the walk `W_{jℓ}` is reversible for the uniform measure on `X(j)`, and every
`B ⊆ X(j)` satisfies `⟨1_B, W_{jℓ} 1_B⟩ ≤ λ|B| + C_mix |B|²/Z_j`.

**Formalization Note.** Standing assumptions of §7 (p.23): `τ ≥ 1`, `X` a regular, `λ`-expanding
`t`-dimensional cubical complex with `t ≥ 2` and degrees `2 ≤ n_1 ≤ ⋯ ≤ n_t`, `n_t/n_1 ≤ τ`. The
constant is the explicit `C_mix` chosen in the proof (p.24), the maximum of `binom(t,p) 2^{t−p−1}
τ^q` over `1 ≤ q < t`, `0 ≤ p ≤ q`. Reversibility for the uniform measure is the symmetry
`W_{jℓ}(f, g) = W_{jℓ}(g, f)`; `⟨1_B, W 1_B⟩ = ∑_{f,g∈B} W(f, g)`. -/
theorem theorem_7_1 {t : ℕ} (ht : 2 ≤ t) {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n) (lam : ℝ) (hexp : IsExpanding φ n lam)
    (τ : ℝ) (hτ : 1 ≤ τ)
    (hratio : (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ) :
    0 < Cmix t τ ∧
    ∀ j ℓ : ℕ, 1 ≤ j → j < t → ℓ ≤ j →
      (∀ f g : Face φ j, faceWalk φ n j ℓ f.1 g.1 = faceWalk φ n j ℓ g.1 f.1) ∧
      ∀ B : Finset (Face φ j),
        ∑ f ∈ B, ∑ g ∈ B, faceWalk φ n j ℓ f.1 g.1 ≤
          lam * (B.card : ℝ) + Cmix t τ * (B.card : ℝ) ^ 2 / (numFaces φ j : ℝ) := by sorry

end GoodQLTC
