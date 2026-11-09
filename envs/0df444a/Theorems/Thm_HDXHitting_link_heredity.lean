-- Prove2me | Theorems.Thm_HDXHitting_link_heredity
-- name    : HDXHitting.link_heredity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:12.53232+00:00
-- url     : https://prove2.me/theorems/f232b975-9db0-4117-804f-a5a08f595cb1
-- title:
--   Links of a (partite) HDX are (partite) HDX of the codimension's dimension
-- statement:
--   Let $p$ be the top distribution of a $d$-dimensional complex $X$, and $\tau$ a face of $X$ (that is, $\Pr_{\sigma\sim p}[\tau\subseteq\sigma]>0$), of codimension $k=d-|\tau|$. Then:
--   1. the link distribution $\pi_\tau$ is the top distribution of a $k$-dimensional complex $X_\tau$;
--   2. if $X$ is a $\lambda$-one-sided HDX, so is $X_\tau$;
--   3. if $X$ is $d$-partite with colouring $c$ and colour set $S$, then $X_\tau$ is $k$-partite with the same colouring and colour set $S\setminus c(\tau)$;
--   4. if moreover $X$ is a $d$-partite $\lambda$-HDX, then $X_\tau$ is a $k$-partite $\lambda$-HDX on the colours $S\setminus c(\tau)$.
--
--   The paper uses this when it applies the induction hypothesis to the vertex link $X_v$, "a $(d-1)$-dimensional $\lambda$-HDX".
--
--   Differences from the source:
--   - encoding: a d-dimensional complex (X, π) given by X and π_d → a top distribution p on Finset V with IsTopDist d p; X(d) = {σ : p σ > 0}; reason: the complex is determined by its top distribution; same instances
--   - encoding: the link X_τ with distribution π_{τ,k} → linkDist p τ, defined for every set τ and used for faces (Pr[τ ⊆ σ] > 0); reason: same object at faces
--   - encoding: second eigenvalue of every link graph at most λ → IsOneSidedHDX: the published Rayleigh-form HDXConc.SecondEigLE on unnormalized link weights for every τ with |τ| + 2 ≤ d; reason: Courant–Fischer for the self-adjoint walk; scale invariance
--   - encoding: X d-partite with parts A_1, …, A_d and µ_i = E_{π_{1|{i}}} f → a colouring c : V → ι with a colour set S, |S| = d, IsRainbow p c S, and colourMean; reason: A_i = c⁻¹(i); a d-face meeting each part at most once meets each exactly once
--   - encoding: second singular value of each colour-pair link graph at most λ → IsPartiteHDX: the Rayleigh-form BipSingLE on the colour-(i, j) link weights; reason: the second singular value is the walk's norm on mean-zero functions; λ ≥ 0
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, p.12 (links; "The partite property is preserved on the links of X"), with Definition 2.2, p.13

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX

namespace HDXHitting

/-- Links inherit the structure (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), §2.2.1, p.12: the link `X_τ` of a face of
codimension `k` is a `k`-dimensional complex, and "The partite property is preserved on the
links of `X`: if `X` is `d`-partite and `τ` is a face with `codim τ = k`, then the link `X_τ` is
`k`-partite"; with Definition 2.2, p.13, whose conditions on the links of `X_τ` are conditions on
links of `X`; used as "`X_v` is a `(d − 1)`-dimensional `λ`-HDX" in the proof of Lemma 3.2): for
a `d`-dimensional complex with top distribution `p` and a face `τ` (`Pr_{σ∼p}[τ ⊆ σ] > 0`), with
`k = d − |τ|`,
1. the link distribution `π_{τ,k}` is the top distribution of a `k`-dimensional complex;
2. if the complex is a `λ`-one-sided HDX, so is the link `X_τ`;
3. if the complex is `d`-partite with colour set `S`, the link is `k`-partite with colour set
   `S ∖ c(τ)` (same colouring);
4. if moreover it is a `d`-partite `λ`-HDX, the link is a `k`-partite `λ`-HDX on `S ∖ c(τ)`. -/
theorem link_heredity {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (τ : Finset V)
    (hτ : 0 < ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => τ ⊆ σ), p σ) (lam : ℝ)
    (c : V → ι) (S : Finset ι) :
    IsTopDist (d - τ.card) (linkDist p τ) ∧
      (IsOneSidedHDX d p lam → IsOneSidedHDX (d - τ.card) (linkDist p τ) lam) ∧
      (IsRainbow p c S → IsRainbow (linkDist p τ) c (S \ τ.image c)) ∧
      (IsRainbow p c S → IsPartiteHDX p c S lam →
        IsPartiteHDX (linkDist p τ) c (S \ τ.image c) lam) := by sorry

end HDXHitting
