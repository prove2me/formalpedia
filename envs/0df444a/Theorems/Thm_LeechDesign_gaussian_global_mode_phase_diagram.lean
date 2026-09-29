-- Prove2me | Theorems.Thm_LeechDesign_gaussian_global_mode_phase_diagram
-- name    : LeechDesign.gaussian_global_mode_phase_diagram
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T04:39:50.549538+00:00
-- url     : https://prove2.me/theorems/b94c23fe-97da-4324-805f-682c419b3c91
-- title:
--   Global Gaussian mode phase diagram of a tight spherical $11$-design in $\mathbb R^{24}$ (Leech configuration): $196560 \to 393120 \to 196560 \to 1$
-- statement:
--   ## Setting
--
--   Work in $\mathbb R^{24}$ with its Euclidean inner product. Let
--
--   $$X = \{x_1,\dots,x_N\} \subset S^{23}, \qquad N = |X| = 196560 = 2\binom{28}{5},$$
--
--   be a **finite set of distinct unit vectors** which is an **equal-weight spherical $11$-design**, expressed here in projection-moment form: for every unit vector $u \in S^{23}$ and every $k \le 11$,
--
--   $$\frac1N \sum_{x \in X} \langle u, x\rangle^{k} \;=\; \int_{S^{23}} z^{k}\,\rho_{24}(dz) \;=\;
--   \begin{cases}
--   0, & k \text{ odd},\\[2mm]
--   \dfrac{(2j-1)!!}{24\cdot 26\cdots (24+2j-2)}, & k = 2j,\ j \le 5,
--   \end{cases}$$
--
--   where $\rho_{24}$ is the law of the first coordinate of the uniform probability measure on $S^{23}$. (Equivalently: $\frac1N\sum_x p(x)=\int_{S^{23}}p\,d\sigma$ for every polynomial $p$ of degree $\le 11$.) Because $N$ equals the odd-strength Fisher number $N_F = 2\binom{28}{5}$, such an $X$ is a **tight** spherical $11$-design. The normalized $196{,}560$ minimal vectors of the Leech lattice form exactly such a configuration; the theorem below is stated for any configuration with these properties, and does **not** assert that one exists.
--
--   For a variance $s>0$ let $f_s$ be the equal-weight Gaussian mixture density stored on $X$,
--
--   $$f_s(x) \;=\; (2\pi s)^{-12}\,\frac{1}{196560}\sum_{y \in X} \exp\!\Big(-\frac{\|x-y\|^2}{2s}\Big),
--   \qquad x \in \mathbb R^{24},$$
--
--   and write $\operatorname{argmax} f_s = \{x : f_s(y) \le f_s(x)\ \text{for all } y\}$ for its set of **global modes**.
--
--   ## Statement
--
--   There exist a variance $S \in \left(0,\tfrac1{24}\right)$, a selected-radius function $r : (0,\tfrac1{24}) \to (0,\infty)$, and two radii $0 < r_1 < r_3$ such that all of the following hold.
--
--   **1. Single shell away from the transition.** For every $s$ with $0 < s < \tfrac1{24}$ and $s \ne S$,
--
--   $$\operatorname{argmax} f_s \;=\; \{\, r(s)\,u : u \in X \,\}, \qquad \bigl|\operatorname{argmax} f_s\bigr| = 196560 .$$
--
--   Every global mode is noncentral, and the global modes sit on a single sphere, one in each stored-node direction.
--
--   **2. Coexistence of two shells at $S$.** At the single variance $s = S$,
--
--   $$\operatorname{argmax} f_S \;=\; \{\, r_1 u : u \in X\,\} \cup \{\, r_3 u : u \in X\,\},
--   \qquad \bigl|\operatorname{argmax} f_S\bigr| = 393120 ,$$
--
--   two distinct nonzero shells carrying $2\cdot 196560$ global modes.
--
--   **3. Only the centre at and above $1/24$.** For every $s \ge \tfrac1{24}$,
--
--   $$\operatorname{argmax} f_s = \{0\}.$$
--
--   **4. The selected radius jumps downward at $S$.**
--
--   $$\lim_{s \uparrow S} r(s) = r_3, \qquad \lim_{s \downarrow S} r(s) = r_1, \qquad r_1 < r_3 .$$
--
--   **5. Continuous square-root collapse at $1/24$.**
--
--   $$\lim_{s \uparrow 1/24} \frac{r(s)}{\sqrt{26\left(\tfrac1{24}-s\right)}} \;=\; 1,
--   \qquad\text{i.e.}\qquad r(s) \sim \sqrt{26\left(\tfrac1{24}-s\right)} .$$
--
--   **6. Every noncentral global mode is nondegenerate.** For every $s \in (0,\tfrac1{24})$ and every $x \in \operatorname{argmax} f_s$ there are $c>0$ and $\delta>0$ with
--
--   $$\log f_s(y) \;\le\; \log f_s(x) - c\,\|y-x\|^2 \qquad \text{whenever } \|y-x\| < \delta .$$
--
--   (For the smooth function $\log f_s$ this is exactly strict negative-definiteness of the Hessian at $x$, i.e. $x$ is a nondegenerate local mode. This applies in particular to *both* shells at $s=S$.)
--
--   **7. The centre at $1/24$ is quartically degenerate.** With the energy normalization $E_s(x) = s\bigl(\log f_s(0) - \log f_s(x)\bigr)$ used throughout the source (so that $f_s \propto e^{-E_s/s}$ and $E_s(0)=0$),
--
--   $$\lim_{x \to 0,\ x \ne 0} \frac{E_{1/24}(x)}{\|x\|^{4}} \;=\; \frac{3}{13},
--   \qquad\text{i.e.}\qquad E_{1/24}(x) = \tfrac3{13}\|x\|^4 + O(\|x\|^6).$$
--
--   So at $s=1/24$ the origin is a *strict* global mode whose Hessian vanishes: the collapse in (5) is a continuous, quartically degenerate one, structurally different from the noncentral-to-noncentral jump at $S$.
--
--   ## What is **not** claimed
--
--   * **No existence claim.** The theorem is conditional on the hypotheses; it does not construct $X$, and it does not assert that a tight spherical $11$-design exists in $\mathbb R^{24}$. (That the normalized Leech minimal vectors are one is a classical geometric input, cited but not reproved in the source, and unavailable in Mathlib.)
--   * **Global modes only.** The counts $196560$, $393120$, $196560$, $1$ count **global maximizers** of $f_s$, not all local modes and not all critical points. The source explicitly disclaims any complete low-noise critical-set or local-mode count.
--   * The companion scalar statements of the same report — $B := \sup_{t>0} 2K(t)/t^2 = \tfrac1{24}$ with no positive attainment, $C := \sup_{t>0} q(t)/t > \tfrac1{24}$ attained at a unique nondegenerate $\tau_C$, the exactly $196561$ critical points at variance $C$, the universal weighted-design uniqueness at variance $1/24$, and the $1/n$ Hopfield convergence rate — are **not** part of this statement.
--   * No uniqueness of $r$, $r_1$, $r_3$, or of $S$ is asserted beyond what the displayed clauses force, and no smoothness or monotonicity of $r$ away from the two stated limits is asserted.
-- source:
--   reports/leech_design_noise_boundaries.md, section 6 "A unique coexistence of two nonzero global shells" (the displayed argmax table, the strict transverse curvature paragraph, and the closing "continuous collapse" paragraph) and section 7 (2026-09-19); independently audited PASS in reports/leech_design_boundaries_audit.md, sections "Two-shell coexistence and curvature" and "Scope and resolved wording". The Gaussian-mixture density convention f_{X,s} is equation (4) of reports/odd_design_tight_boundary_theorem.md section 1, whose section 3 supplies the Fisher-equality argument identifying |X| = 2*binom(28,5) = 196560 with tightness; the energy normalization E_s(x) = s*(log f_s(0) - log f_s(x)) used in clause 7 is equation (1) of reports/odd_design_hopfield_dynamics.md. Finite arithmetic reproduced by experiments/verify_leech_design_boundaries.py and reports/leech_design_boundaries_certificate.json.

import Mathlib

open Filter Topology

theorem LeechDesign.gaussian_global_mode_phase_diagram
    (X : Finset (EuclideanSpace ℝ (Fin 24)))
    (f : ℝ → EuclideanSpace ℝ (Fin 24) → ℝ)
    (hcard : X.card = 196560)
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hodd : ∀ u : EuclideanSpace ℝ (Fin 24), ‖u‖ = 1 → ∀ k ≤ 11, Odd k →
      ∑ x ∈ X, (inner ℝ u x : ℝ) ^ k = 0)
    (heven : ∀ u : EuclideanSpace ℝ (Fin 24), ‖u‖ = 1 → ∀ j ≤ 5,
      ∑ x ∈ X, (inner ℝ u x : ℝ) ^ (2 * j)
        = 196560 * (Nat.doubleFactorial (2 * j - 1) : ℝ)
            / ∏ i ∈ Finset.range j, ((24 : ℝ) + 2 * (i : ℝ)))
    (hf : ∀ s : ℝ, 0 < s → ∀ x : EuclideanSpace ℝ (Fin 24),
      f s x = ((2 * Real.pi * s) ^ (12 : ℕ))⁻¹ * (196560 : ℝ)⁻¹ *
        ∑ y ∈ X, Real.exp (-‖x - y‖ ^ 2 / (2 * s))) :
    ∃ S ∈ Set.Ioo (0 : ℝ) (1 / 24), ∃ r : ℝ → ℝ, ∃ r₁ r₃ : ℝ,
      0 < r₁ ∧ r₁ < r₃ ∧
      (∀ s : ℝ, 0 < s → s < 1 / 24 → s ≠ S →
        0 < r s ∧
        {x | ∀ y, f s y ≤ f s x}
            = (fun u => r s • u) '' (X : Set (EuclideanSpace ℝ (Fin 24))) ∧
        Set.ncard {x | ∀ y, f s y ≤ f s x} = 196560) ∧
      ({x | ∀ y, f S y ≤ f S x}
          = (fun u => r₁ • u) '' (X : Set (EuclideanSpace ℝ (Fin 24)))
            ∪ (fun u => r₃ • u) '' (X : Set (EuclideanSpace ℝ (Fin 24)))) ∧
      Set.ncard {x | ∀ y, f S y ≤ f S x} = 393120 ∧
      (∀ s : ℝ, 1 / 24 ≤ s →
        {x | ∀ y, f s y ≤ f s x} = ({0} : Set (EuclideanSpace ℝ (Fin 24)))) ∧
      Filter.Tendsto r (𝓝[<] S) (𝓝 r₃) ∧
      Filter.Tendsto r (𝓝[>] S) (𝓝 r₁) ∧
      Filter.Tendsto (fun s => r s / Real.sqrt (26 * (1 / 24 - s)))
        (𝓝[<] (1 / 24 : ℝ)) (𝓝 1) ∧
      (∀ s : ℝ, 0 < s → s < 1 / 24 → ∀ x, (∀ y, f s y ≤ f s x) →
        ∃ c > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ →
          Real.log (f s y) ≤ Real.log (f s x) - c * ‖y - x‖ ^ 2) ∧
      Filter.Tendsto
        (fun x : EuclideanSpace ℝ (Fin 24) =>
          (1 / 24 : ℝ) * (Real.log (f (1 / 24) 0) - Real.log (f (1 / 24) x)) / ‖x‖ ^ 4)
        (𝓝[≠] (0 : EuclideanSpace ℝ (Fin 24))) (𝓝 (3 / 13)) := by sorry
