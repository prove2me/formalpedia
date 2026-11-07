-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_7
-- name    : LowTempGlauber.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:07.049758+00:00
-- url     : https://prove2.me/theorems/cf7a0223-95e5-4e14-b20a-4ba329e4e24e
-- title:
--   Lemma 7 — an $(A,b+\delta)$ weak Poincaré inequality for Glauber dynamics on $\mathcal I^+_G$
-- statement:
--   Let $d\ge3$ and $\lambda>1$. Let $G=(V^+\sqcup V^-,E)$ be any $d$-regular bipartite graph with $|V^\pm|=n$ and vertex activities $0<\lambda_v\le\lambda$; let $\mu$ be the hard-core law on $G$, $\mu^+=\mu(\cdot\mid\mathcal I^+)$, and $P^+$ single-site Glauber dynamics on $\mathcal I^+_G$ with proposals outside $\mathcal I^+_G$ rejected. For integers $\ell,r\ge1$ and real $\theta\in(0,1/2)$, let
--   $$b=\Pr\bigl[(I,J)\in B_{\ell,r}\cup H_\theta\bigr],\qquad H_\theta=\{(I,J):I\text{ or }J\in\mathcal I^{\mathrm{bal}}(\theta)\},$$
--   for independent $I,J\sim\mu^+$. Then for every $f:\mathcal I^+\to\mathbb R$
--   $$\operatorname{Var}_{\mu^+}(f)\le A\,\mathcal E_{P^+}(f,f)+(b+\delta)(f_{\max}-f_{\min})^2,$$
--   where $A=8n(d\ell\lambda)^{k+1}$ with $k=r+4d\ln\ell$, and $\delta=4n\,e^{-\theta^2n/(4\ell)}$.
--
--   Combined with Theorem 6, which makes $b$ polynomially small for $\ell,r$ of logarithmic and constant size, this gives a weak Poincaré inequality with $A=n^{1+o(1)}$ uniformly along the annealing schedule.
--
--   **Formalization Note** The state space is $\mathcal I^+_G$ itself, so $f$, $f_{\max}$, $f_{\min}$, the variance and the Dirichlet form are taken over $\mathcal I^+_G$. The exponent $k+1$ is real, $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: P⁺, Glauber dynamics on I⁺_G with proposals outside I⁺_G rejected → glauber μ⁺ restricted to the subtype I⁺_G (subChain); reason: the same transition matrix on I⁺_G
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 7, pp.9–10

import Mathlib
import Definitions.Def_mm_mcmc
import Definitions.Def_mm_coupling
import Definitions.Def_LowTempGlauber_ChainLayer
import Definitions.Def_LowTempGlauber_Disagreement

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 7, pp.9–10.

Let `d ≥ 3` and `λ > 1`. For every `d`-regular bipartite graph `G = (V⁺ ⊔ V⁻, E)` with `|V±| = n` and
activities `0 < λ_v ≤ λ`, let `μ` be the hard-core law, `μ⁺ = μ(· | I⁺)` and `P⁺` single-site Glauber
dynamics on `I⁺_G` with proposals outside `I⁺_G` rejected. For integers `ℓ, r ≥ 1` and real
`θ ∈ (0, 1/2)` let `b = Pr[(I, J) ∈ B_{ℓ,r} ∪ H_θ]` for independent `I, J ∼ μ⁺`
(`H_θ`: `I` or `J` in `I^bal(θ)`). Then for every `f : I⁺ → ℝ`
`Var_{μ⁺}(f) ≤ A E_{P⁺}(f, f) + (b + δ)(f_max − f_min)²` (4),
with `A = 8n(dℓλ)^{k+1}`, `k = r + 4d ln ℓ` and `δ = 4n e^{−θ²n/(4ℓ)}`.

**Formalization Note.** The state space is the subtype `I⁺_G`, so `f`, `f_max`, `f_min`, the variance
and the Dirichlet form are over `I⁺_G` only. `P⁺` is `glauber μ⁺` restricted to `I⁺_G` (`subChain`);
heat-bath Glauber for `μ⁺` is heat-bath Glauber for `μ` with moves leaving `I⁺` rejected. `k` is real
and `(dℓλ)^{k+1}` is a real power. -/
theorem lemma_7 (n d : ℕ) (hd : 3 ≤ d) (G : SimpleGraph (Vertex n)) (hG : IsBipReg G d)
    (lam : ℝ) (hlam : 1 < lam) (act : Vertex n → ℝ) (hact : ∀ v, 0 < act v ∧ act v ≤ lam)
    (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    (f : {σ : Vertex n → Bool // IPlus G σ} → ℝ) :
    variance (fun x => condLaw (hcLaw G act) (IPlus G) x.1) f ≤
      (8 * n * ((d : ℝ) * ℓ * lam) ^ ((r : ℝ) + 4 * d * Real.log ℓ + 1)) *
          dirichlet (subChain (glauber (condLaw (hcLaw G act) (IPlus G))) (IPlus G))
            (fun x => condLaw (hcLaw G act) (IPlus G) x.1) f +
        ((∑ x : {σ : Vertex n → Bool // IPlus G σ}, ∑ y : {σ : Vertex n → Bool // IPlus G σ},
            if BadComp G ℓ r x.1 y.1 ∨ Ibal G θ x.1 ∨ Ibal G θ y.1 then
              condLaw (hcLaw G act) (IPlus G) x.1 * condLaw (hcLaw G act) (IPlus G) y.1 else 0) +
          4 * n * Real.exp (-(θ ^ 2 * n) / (4 * ℓ))) * osc f ^ 2 := by sorry

end LowTempGlauber
