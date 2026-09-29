-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
-- name    : ModularCurve.FullLevel.exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/e77bebea-0ed6-55f5-889e-bbeec6c09a00
-- title:
--   Shimura reciprocity for f∣_kγ^sharp at full level
-- statement:
--   Let $q$ be a prime and $M'$ a natural number with $q \nmid M'$, and let $k$ be an even integer. Write $H =$ `levelH q M'` for the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and let $\Gamma =$ [`CohCarrier.GammaH (q ^ 2 * M') (levelH q M')`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$, viewed inside $\mathrm{GL}_2(\mathbb{R})$, consisting of those $\gamma \in \Gamma_0(q^2M')$ whose lower right entry, as a unit mod $q^2M'$, lies in $H$, i.e. is $\equiv 1 \bmod q$. Let $f$ be a modular form of weight $k$ on $\Gamma$ all of whose $q$-expansion coefficients at width $1$ (parameter $e^{2\pi i \tau}$) are rational, and let $\gamma \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$. Then there is a family $h : \mathbb{N} \to$ (modular forms of weight $k$ on $\Gamma$), each $h_j$ again with all width-$1$ $q$-expansion coefficients rational, such that for every natural number $s$ coprime to $q$ and every $\gamma' \in \Gamma_0(M')$ satisfying $\mathrm{diag}(1,s)\,\bar{\gamma'} = \bar{\gamma}\,\mathrm{diag}(1,s)$ in $M_2(\mathbb{Z}/q)$ (entrywise reduction), one has, as functions on the upper half-plane,
--   $$f \mid_k \mathrm{conjElem}(q,\gamma') \;=\; \sum_{j=0}^{q-1} e^{2\pi i s j/q}\, h_j,$$
--   where $\mathrm{conjElem}(q,\gamma')$ is the determinant-one real matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ attached to $\gamma' = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, that is $\mathrm{diag}(q,1)^{-1}\gamma'\,\mathrm{diag}(q,1)$. Only the values $h_j$ for $j < q$ enter the conclusion.
--
--   This is Shimura's reciprocity law at the cusps, transported from $\Gamma(q) \cap \Gamma_0(M')$ to the level-$\Gamma_H(q^2M')$ picture by $\tau \mapsto \tau/q$: the Fourier coefficients of $f \mid_k \gamma^\sharp$ lie in $\mathbb{Q}(e^{2\pi i/q})$, and the Galois action $e^{2\pi i/q} \mapsto e^{2\pi i s/q}$ on them is realised by replacing $\gamma$ by a matrix $\gamma'$ congruent to it after twisting by $\mathrm{diag}(1,s)$. It is used, via the decomposition into the $h_j$, by [`ModularCurve.FullLevel.exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0`](thm.html#ModularCurve.FullLevel.exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0), in the analysis of the rational structure on the full-level modular curve and its Jacobian; the proof cites the corresponding reciprocity statement for even-weight forms on $\Gamma(N)$ together with surjectivity of $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ h : ℕ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
        Subgroup (GL (Fin 2) ℝ)) k,
      (∀ j n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (h j)).coeff n = (r : ℂ)) ∧
      ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s q → γ' ∈ CongruenceSubgroup.Gamma0 M' →
        !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
          = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)] →
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElem q γ') =
          ∑ j ∈ Finset.range q,
            Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) •
              (⇑(h j) : UpperHalfPlane → ℂ) := by sorry
