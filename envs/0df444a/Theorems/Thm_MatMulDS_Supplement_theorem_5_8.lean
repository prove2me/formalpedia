-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_5_8
-- name    : MatMulDS.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:15:32.887309+00:00
-- url     : https://prove2.me/theorems/6a65f662-a11f-4116-b01a-76f101bb2909
-- title:
--   Theorem 5.8 — data structures from a base identity (all three items)
-- statement:
--   Fix a block tensor $T_{\mathrm{base}}$ with an identity and a private map, over a field $\mathbb F$ of characteristic zero. For items 1 and 2, also fix a compatible weight function, a distribution $\pi$ on $O$ with rational values that is uniform within each block and has $\mathrm{len}(\pi)>0$, a threshold $0\le\eta_{\mathrm{pre}}\le\mu$ and $\theta\ge0$, and let $\nu,E,\Gamma,Q$ be the rates of §§5.4–5.5. $\tilde O$ hides factors polynomial in $\log N$.
--
--   1. *(One middle block.)* For every fixed $\Delta<1/\nu$ and $2\le D\le N^\Delta$, arbitrary $A\in\mathbb F^{N\times D}$, $B\in\mathbb F^{D\times N}$ admit a deterministic data structure with preprocessing time and space $\tilde O(ND^E+N^2D^{-\Gamma})$ and worst-case query time $\tilde O(D^Q)$ for adaptive queries; any $M$ entries of $AB$ are computed in $\tilde O(ND^E+N^2D^{-\Gamma}+MD^Q)$ time.
--   2. *(Many middle blocks.)* Suppose $\omega(1,s,1)\le2+\rho(s)$ for all $s\ge0$. Fix $0<\delta_0\le\delta$ with $\nu\delta_0<1$ and let
--   $$p_{\mathrm{enc}}=1+\delta+\delta_0(E-1),\quad p_{\mathrm{tab}}=2-\delta_0\Gamma+(1-\nu\delta_0)\,\rho\Big(\frac{\delta-\delta_0}{1-\nu\delta_0}\Big),\quad q_{\mathrm{query}}=\delta-\delta_0(1-Q).$$
--   Then for $D=N^\delta$ there is a deterministic data structure with preprocessing time and space $N^{\max\{p_{\mathrm{enc}},p_{\mathrm{tab}}\}+o(1)}$ and query time $N^{q_{\mathrm{query}}+o(1)}$; any $M=N^\zeta$ entries are computed in $N^{\max\{p_{\mathrm{enc}},p_{\mathrm{tab}},\zeta+q_{\mathrm{query}}\}+o(1)}$ time.
--   3. *(The score.)* If the identity is bijective, admits a strict compatible weight function and has score $\sigma>0$, then for all fixed $0<\delta<\sigma$ and $q_0>0$ there is $\gamma>0$ such that for $D=N^\delta$ there is a data structure with preprocessing time and space $O(N^{2-\gamma})$ and query time $O(D^{q_0})$, without any bound on rectangular matrix multiplication. Moreover, with the bound of Proposition 4.5, there are $\delta_1,\gamma_1>0$ such that for $D=N^{1/2+\delta_1}$ there is one with preprocessing $O(N^{2-\gamma_1})$ and query $O(N^{1/2-\gamma_1})$.
--
--   All these data structures are given by bilinear data structures. The theorem reduces the construction of data structures to four rates of a base identity, and its item 2 is how Theorems 7.4 and 7.5 are obtained.
--
--   **Formalization Note** Item 1 states the bilinear family, its machine counterpart (`IsMatMulOracle`, `AnswersListWithin`) and the bound for every list of queries; items 2 and 3 state the bilinear families, which give deterministic data structures.
--
--   Differences from the source:
--   - reading: uniform circuits and the machine data structure, with weights and threshold "fixed" → those clauses take $\mathrm{wt}$ and $\eta_{\mathrm{pre}}$ rational; the circuit bounds hold for all reals; reason: as in the published Theorem A.7: the construction computes the light strings, which determine $\lfloor2L\eta_{\mathrm{pre}}\rfloor$ for all $L$, so no fixed finite program follows it for an uncomputable threshold; the source only uses exact decimals
--   - encoding: $\Delta<1/\nu$ → $\Delta\nu<1$; reason: the same for $\nu>0$; for $\nu=0$ the source's $1/\nu$ is infinite while Lean's $1/0$ is $0$
--   - encoding: $\tilde O(X)$, polylog $N$; $N^{x+o(1)}$ → $C(\log N+1)^cX$; for every $\varepsilon>0$ a $C$ with $CN^{x+\varepsilon}$, for one family fixed before $\varepsilon$; reason: the meaning of these symbols for one fixed construction
--   - encoding: $D=N^\delta$, $D=N^{1/2+\delta_1}$; $M=N^\zeta$ → $D=\lceil N^\delta\rceil$, $D=\lceil N^{1/2+\delta_1}\rceil$; every list of at most $N^\zeta$ queries, $\zeta\ge0$; reason: dimensions are rounded as in §4.2
--   - reading: "This does not use any bound on rectangular matrix multiplication"; "without using any bound" → conclusions with no hypothesis on $\omega$; reason: remarks on the proof; the statements assume nothing about $\omega$
--   - reading: "with the bound on rectangular matrix multiplication from Proposition 4.5" → no hypothesis; reason: it names a cited theorem the proof uses (SUPPLEMENT decision 2)
--   - generalization: "admits a strict compatible weight function" for the fixed private map → some private map with a strict compatible weight function (`HasStrictWeight`); reason: a weaker hypothesis; the source's case is the instance with the fixed private map
--   - encoding: "admit a deterministic data structure"; "given by bilinear data structures" → families of `BilinearDS` with the bounds on $T_{\mathrm{pre}}$ (preprocessing and space) and $T_{\mathrm{query}}$, and in item 1 also the machine data structure; reason: a bilinear data structure gives the deterministic one by evaluating its circuits
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 5.8, eq. (5.6), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData
import Definitions.Def_MatMulDS_IsEnlargement
import Definitions.Def_MatMulDS_UniformFamily
import Definitions.Def_MatMulDS_omegaExp

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Theorem 5.8 (Data Structures from a Base Identity), p.34** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission,
held file sha256 6c5a1c16…). Fix a block tensor `T_base` with an identity and a private map. For items (i) and (ii), also fix a
compatible weight function, a distribution `π` on `O` with rational values that is uniform within each block and has `len(π) > 0`,
a threshold `0 ≤ η_pre ≤ µ` and a parameter `θ ≥ 0`, and let `ν, E, Γ, Q` be the rates of §§5.4–5.5.
(i) For every fixed `Δ < 1/ν` and `2 ≤ D ≤ N^Δ`, arbitrary `A ∈ F^{N×D}`, `B ∈ F^{D×N}` admit a deterministic data structure with
preprocessing time and space `Õ(N D^E + N² D^{−Γ})` and worst-case query time `Õ(D^Q)` for adaptive queries; any `M` entries of
`AB` are computed in `Õ(N D^E + N² D^{−Γ} + M D^Q)` time.
(ii) If `ω(1, s, 1) ≤ 2 + ρ(s)` for all `s ≥ 0`, then for fixed `0 < δ0 ≤ δ` with `νδ0 < 1` and the exponents (5.6), for
`D = N^δ` there is such a data structure with preprocessing time and space `N^{max{p_enc, p_tab}+o(1)}` and query time
`N^{q_query+o(1)}`; any `M = N^ζ` entries are computed in `N^{max{p_enc, p_tab, ζ+q_query}+o(1)}` time.
(iii) If the identity is bijective, admits a strict compatible weight function and has score `σ > 0`, then for all fixed
`0 < δ < σ` and `q0 > 0` there is `γ > 0` with, for `D = N^δ`, preprocessing time and space `O(N^{2−γ})` and query time
`O(D^{q0})`; moreover, with the bound of Proposition 4.5, there are `δ1, γ1 > 0` with, for `D = N^{1/2+δ1}`, preprocessing
`O(N^{2−γ1})` and query `O(N^{1/2−γ1})`.
All these data structures are given by bilinear data structures, over every field of characteristic zero; `Õ` hides factors
polynomial in `log N`.

**Formalization Note.**
* `Õ(X)` is `C (log N + 1)^c X` with `C, c` fixed before `N, D`; `N^{x+o(1)}` is: for every `ε > 0` some `C` with `C N^{x+ε}`,
  for the one family `ds` fixed before `ε`.
* `Δ < 1/ν` is `Δ ν < 1` (`1/0 = 0` in Lean); `D = N^δ` is `D = ⌈N^δ⌉`; `M = N^ζ` is every list of at most `N^ζ` queries.
* A bilinear data structure gives the deterministic one (its circuits are evaluated; `AdmitsDS`, `IsMatMulOracle`). The uniform
  families and the machine data structure of (i), (ii) take `wt`, `η_pre` rational, as in the published Theorem A.7; the circuit
  bounds hold for all real values.
* "This does not use any bound on rectangular matrix multiplication" (in (i) and (iii)) is a remark on the proof: those
  conclusions assume nothing about `ω`. The second claim of (iii) is stated without hypothesis: the bound of Proposition 4.5 is a
  cited theorem, not an assumption. -/
theorem theorem_5_8 (F : Type) [Field F] [CharZero F] [DecidableEq F] (T : BlockTensor I K J B)
    (D : IdentityData I K J P) (hD : D.Computes T) (ρ : T.Out → P) (hρ : D.IsPrivateMap T ρ) :
    (∀ (wt : P → ℝ), D.IsCompatible T ρ wt → ∀ (π : I × J → ℚ), IsBlockDistribution T π → 0 < lenPi T π →
      ∀ η : ℝ, 0 ≤ η → η ≤ mu π ρ wt → ∀ θ : ℝ, 0 ≤ θ →
      let f := fRate wt θ η
      let ξ := xiRate D π ρ wt η
      let ν := nuRate T π
      let E := eRate T P π
      let Γ := gammaRate T π f
      let Q := qRate T π ξ
      -- (i) one middle block
      (∀ Δ : ℝ, Δ * ν < 1 →
        ∃ (c : ℕ) (C : ℝ)
          (ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ}, BilinearDS F x.1.1 x.1.2),
          0 < C ∧
          (∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ},
            ((ds x).Tpre : ℝ) ≤ C * (Real.log x.1.1 + 1) ^ c *
              ((x.1.1 : ℝ) * (x.1.2 : ℝ) ^ E + (x.1.1 : ℝ) ^ 2 * (x.1.2 : ℝ) ^ (-Γ)) ∧
            ((ds x).Tquery : ℝ) ≤ C * (Real.log x.1.1 + 1) ^ c * (x.1.2 : ℝ) ^ Q) ∧
          ((∀ p, ∃ q : ℚ, wt p = q) → (∃ q : ℚ, η = q) →
            UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ} => x.1.1)
              (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
            ∃ (O : AOracle) (cs : List F) (K' : ℕ),
              IsMatMulOracle O cs K' (fun N Dm => 2 ≤ Dm ∧ (Dm : ℝ) ≤ (N : ℝ) ^ Δ)
                (fun N Dm => C * (Real.log N + 1) ^ c * ((N : ℝ) * (Dm : ℝ) ^ E + (N : ℝ) ^ 2 * (Dm : ℝ) ^ (-Γ)))
                (fun N Dm => C * (Real.log N + 1) ^ c * (Dm : ℝ) ^ Q) ∧
              ∀ (N Dm : ℕ), 1 ≤ N → 2 ≤ Dm → (Dm : ℝ) ≤ (N : ℝ) ^ Δ →
              ∀ (A : Matrix (Fin N) (Fin Dm) F) (B' : Matrix (Fin Dm) (Fin N) F) (w : ℕ),
                K' * Nat.clog 2 (N + 1) + K' ≤ w →
                ∀ qs : List (Fin N × Fin N),
                  AnswersListWithin O cs w A B' qs
                    (C * (Real.log N + 1) ^ c *
                      ((N : ℝ) * (Dm : ℝ) ^ E + (N : ℝ) ^ 2 * (Dm : ℝ) ^ (-Γ) + (qs.length : ℝ) * (Dm : ℝ) ^ Q)))) ∧
      -- (ii) many middle blocks
      (∀ ϱ : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ ϱ s) → (∀ s, 0 ≤ s → omegaExp F 1 s 1 ≤ 2 + ϱ s) →
        ∀ δ0 δ : ℝ, 0 < δ0 → δ0 ≤ δ → ν * δ0 < 1 →
        let p_enc := 1 + δ + δ0 * (E - 1)
        let p_tab := 2 - δ0 * Γ + (1 - ν * δ0) * ϱ ((δ - δ0) / (1 - ν * δ0))
        let q_query := δ - δ0 * (1 - Q)
        ∃ ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ x.2 = ⌈(x.1 : ℝ) ^ δ⌉₊}, BilinearDS F x.1.1 x.1.2,
          ((∀ p, ∃ q : ℚ, wt p = q) → (∃ q : ℚ, η = q) →
            UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ x.2 = ⌈(x.1 : ℝ) ^ δ⌉₊} => x.1.1)
              (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1))) ∧
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
            ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ x.2 = ⌈(x.1 : ℝ) ^ δ⌉₊},
              ((ds x).Tpre : ℝ) ≤ C * (x.1.1 : ℝ) ^ (max p_enc p_tab + ε) ∧
              ((ds x).Tquery : ℝ) ≤ C * (x.1.1 : ℝ) ^ (q_query + ε) ∧
              ∀ (ζ : ℝ) (M : ℕ), 0 ≤ ζ → (M : ℝ) ≤ (x.1.1 : ℝ) ^ ζ →
                (((ds x).Tpre + M * (ds x).Tquery : ℕ) : ℝ) ≤
                  C * (x.1.1 : ℝ) ^ (max (max p_enc p_tab) (ζ + q_query) + ε))) ∧
    -- (iii) the score
    (IsBijective T P → HasStrictWeight T D → 0 < score T P →
      (∀ δ q0 : ℝ, 0 < δ → δ < score T P → 0 < q0 →
        ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
          AdmitsDS F (fun N Dm => 1 ≤ N ∧ Dm = ⌈(N : ℝ) ^ δ⌉₊)
            (fun N _ => C * (N : ℝ) ^ (2 - γ)) (fun _ Dm => C * (Dm : ℝ) ^ q0)) ∧
      ∃ δ1 γ1 : ℝ, 0 < δ1 ∧ 0 < γ1 ∧ ∃ C : ℝ, 0 < C ∧
        AdmitsDS F (fun N Dm => 1 ≤ N ∧ Dm = ⌈(N : ℝ) ^ ((1 : ℝ) / 2 + δ1)⌉₊)
          (fun N _ => C * (N : ℝ) ^ (2 - γ1)) (fun N _ => C * (N : ℝ) ^ ((1 : ℝ) / 2 - γ1))) := by sorry

end MatMulDS.Supplement
