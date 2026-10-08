-- Prove2me | Theorems.Thm_FournierGuillin_Conc_proposition_8
-- name    : FournierGuillin.Conc.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:20.485117+00:00
-- url     : https://prove2.me/theorems/8fbed888-425d-49c0-abf0-9620304de7a6
-- title:
--   Proposition 8, p. 10 — ℙ(Π_N(ℝ^d)𝒟_p(Ψ_N, μ) ≥ Nx) ≤ C exp(−Nf(cx)) (+ exp(−cNx^{d/p})) for the Poissonized compact case
-- statement:
--   Let $d\ge1$ and let $p>0$ with $p\ge d/2$ or $p\ge1$. There are constants $C,c>0$, depending only on $d$ and $p$, such that the following holds. Let $\mu$ be a probability measure supported in $(-1,1]^d$, let $\Pi_N$ be a Poisson measure on $\mathbb R^d$ with intensity $N\mu$, and let $\Psi_N=(\Pi_N(\mathbb R^d))^{-1}\Pi_N$ be its empirical measure. For all integers $N\ge1$ and all $x>0$,
--   $$\mathbb P\big(\Pi_N(\mathbb R^d)\,\mathcal D_p(\Psi_N,\mu)\ge Nx\big)\le C\times\begin{cases}\exp(-Nf(cx)) & p>d/2,\\ \exp\big(-Nf(cx/\log(2+1/x))\big) & p=d/2,\\ \exp(-Nf(cx))+\exp(-cNx^{d/p}) & p\in[1,d/2),\end{cases}$$
--   where $\mathcal D_p$ is the compact distance of Notation 4(a) and $f$ is as in Notation 7.
--
--   This is the concentration inequality in the Poissonized compact case; independence of the cell counts of a Poisson measure is what makes it accessible, and Proposition 10 removes the Poissonization.
--
--   **Formalization Note** $\Pi_N$ is represented by its law: Poisson($N$)-many points, i.i.d. $\mu$ given their number $n$; on a configuration of $n$ points, $\Pi_N(\mathbb R^d)\mathcal D_p(\Psi_N,\mu)$ is $n$ times `Dcube` of the configuration's empirical measure and $\mu$, which is $0$ at $n=0$ (where $\Psi_N$ is undefined on the page; the event is then empty since $Nx>0$). "Supported in $(-1,1]^d$" is $\mu(((-1,1]^d)^c)=0$. **Range:** the page states "Let $p\ge1$"; here the proposition is posed for $p\ge d/2$ or $p\ge1$, adding $d=1$, $p\in[1/2,1)$. Its proof never uses $p\ge1$ (only $2^p>1$ and the comparison of $p$ with $d/2$), and Theorem 2's proof applies it for every $p>d/2$. The constants $C,c$ are quantified before $\mu$, $N$ and $x$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proposition 8, p. 10; proof pp. 10–12; Π_N represented as on p. 13 (proof of Proposition 10, Step 1)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Proposition 8 (p. 10): for `μ` supported in `(-1, 1]^d`, `Π_N` the Poisson measure with
intensity `Nμ` and `Ψ_N = Π_N/Π_N(ℝ^d)`, there are `C, c > 0` depending only on `d, p` such that for
all `N ≥ 1` and `x > 0`, `ℙ(Π_N(ℝ^d) 𝒟_p(Ψ_N, μ) ≥ Nx) ≤ C × rate8`, with `𝒟_p` the compact
distance `Dcube`. Posed for `p ≥ d/2` or `p ≥ 1` (the page has "`p ≥ 1`"; see the mission notes).
For a configuration of `n` points, `Π_N(ℝ^d) 𝒟_p(Ψ_N, μ) = n · FournierGuillin.Moment.Dcube p (empirical measure) μ`. -/
theorem proposition_8 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p)
    (hrange : (d : ℝ) / 2 ≤ p ∨ 1 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], μ (FournierGuillin.Moment.shell 0)ᶜ = 0 →
        ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
          poissonProb (N : ℝ≥0) μ
              (fun n => {ω : Fin n → EuclideanSpace ℝ (Fin d) |
                ENNReal.ofReal (N * x) ≤ (n : ℝ≥0∞) * FournierGuillin.Moment.Dcube p (empiricalDistribution ω) μ}) ≤
            ENNReal.ofReal (C * rate8 d p c N x) := by sorry

end FournierGuillin.Conc
