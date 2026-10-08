-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_theorem_12
-- name    : LambdaCoalescent.CoagFrag.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:27.10847+00:00
-- url     : https://prove2.me/theorems/f4117037-c0f2-4493-9f07-3a804e034d48
-- title:
--   Theorem 12, p. 1878 — an (α, θ) partition coagulated by (β, θ/α) has the joint law of an (αβ, θ) partition fragmented by (α, −αβ)
-- statement:
--   Let $0<\alpha<1$, $0\le\beta<1$ and $\theta>-\alpha\beta$. For a pair $(\Pi,\Pi')$ of random partitions of $\mathbb N$ the following conditions are equivalent:
--
--   1. $\Pi$ is an $(\alpha,\theta)$ partition and $\Pi'$ is a $(\beta,\theta/\alpha)$-coagulation of $\Pi$;
--   2. $\Pi'$ is an $(\alpha\beta,\theta)$ partition and $\Pi$ is an $(\alpha,-\alpha\beta)$-fragmentation of $\Pi'$.
--
--   Here an $(\alpha,\theta)$ partition is an exchangeable random partition with EPF $p_{\alpha,\theta}$ of (15); $\Pi'$ is a $(\beta,\theta/\alpha)$-coagulation of $\Pi$ if, given $\Pi=\pi$, $\Pi'$ is the $\gamma$-coagulation of $\pi$ for an independent $\gamma$ with law $p_{\beta,\theta/\alpha}$ (Definition 5); and $\Pi$ is an $(\alpha,-\alpha\beta)$-fragmentation of $\Pi'$ if, given $\Pi'=\pi'$, $\Pi$ is obtained by restricting independent partitions $\Gamma^{(1)},\Gamma^{(2)},\dots$ with law $p_{\alpha,-\alpha\beta}$ to the successive blocks of $\pi'$ (Definition 11).
--
--   Since each condition fixes the joint law of $(\Pi,\Pi')$, the theorem says that two measures on $\mathcal P_\infty\times\mathcal P_\infty$ coincide: if $\mu,\nu,\rho,\kappa$ are the laws with EPFs $p_{\alpha,\theta}$, $p_{\beta,\theta/\alpha}$, $p_{\alpha\beta,\theta}$, $p_{\alpha,-\alpha\beta}$, then for every measurable $S\subseteq\mathcal P_\infty\times\mathcal P_\infty$,
--   $$(\mu\otimes\nu)\{(\pi,\gamma):(\pi,\ \gamma\text{-coag of }\pi)\in S\}=\big(\rho\otimes\kappa^{\otimes\mathbb N}\big)\{(\pi',\Gamma):(\Gamma\text{-frag of }\pi',\ \pi')\in S\}.$$
--
--   The theorem describes one joint law of a pair of exchangeable partitions, $\Pi$ refining $\Pi'$, from both ends; with $\beta=0$ it links the $(\alpha,\theta)$ family to Ewens' $(0,\theta)$ family, and through Kingman's correspondence it gives the Poisson–Dirichlet statement of Corollary 13.
--
--   **Formalization Note** "(i) $\Leftrightarrow$ (ii) for every pair $(\Pi,\Pi')$" is the equality of the two joint laws: each condition determines the joint law (conditional laws given $\Pi=\pi$ are meaningful only almost surely, so the conditions are encoded through joint laws), and each law is realized on the canonical space, so the equivalence for all pairs and the equality of laws imply each other. The equality is stated through (outer) measures of preimages of measurable sets. The four laws exist by Lemma 9, so the hypotheses are not vacuous; all four parameter pairs satisfy (14) under the hypotheses ($\theta/\alpha>-\beta$, $-\alpha\beta>-\alpha$). $\theta/\alpha$ is a real division with $\alpha>0$. The fragmenting partitions are an i.i.d. sequence, one sample of `Measure.infinitePi (fun _ => κ)`, indexed from $0$ in the order of least elements of the blocks of $\Pi'$. EPFs are in the cancelled form of the Setting module, which matters at $\beta=0$.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1878, Theorem 12 (with Definitions 5, 11 and the (α, θ) notation of p. 1878)

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem theorem_12 (α β θ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ : -(α * β) < θ)
    (μ ν ρ κ : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ]
    (hμ : IsEPFLaw (pdEPF α θ) μ) (hν : IsEPFLaw (pdEPF β (θ / α)) ν)
    (hρ : IsEPFLaw (pdEPF (α * β) θ) ρ) (hκ : IsEPFLaw (pdEPF α (-(α * β))) κ) :
    ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
      (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S} =
        (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))) {y | (frag y.1 y.2, y.1) ∈ S} := by sorry

end LambdaCoalescent.CoagFrag
