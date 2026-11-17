-- Prove2me | Theorems.Thm_LowTempGlauber_Supplement_theorem_2
-- name    : LowTempGlauber.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:28:35.460102+00:00
-- url     : https://prove2.me/theorems/04ba85fc-df2e-4750-9e42-091f0c2a6c41
-- title:
--   Theorem 2 — random-cluster Glauber dynamics ($q>2$) on random $d$-regular graphs samples each phase near $\beta_c$ in $n^{3/2+o(1)}$ steps; the full law in $n^{2+o(1)}$ time
-- statement:
--   Fix an integer $d\ge3$ and a real $q>2$, and write $\beta_c=\beta_c(q,d)=\log\frac{q-2}{(q-1)^{1-2/d}-1}$. Let $\pi_G$ be the random-cluster law $\pi_G(F)\propto(e^\beta-1)^{|F|}q^{\kappa(F)}$ on edge sets of $G$, and $\pi^\pm_G=\pi_G(\cdot\mid E^\pm_G)$ its phases, $E^+_G=\{|F|>\frac{dn}2m_c\}$ and $E^-_G=\{|F|\le\frac{dn}2m_c\}$ with the critical edge density $m_c$ of Remark 41. Let $G$ be a uniformly random $d$-regular graph on $n$ vertices.
--
--   There is $\delta>0$ such that for every $K>0$, with $\varepsilon=n^{-K}$:
--   1. for every $\beta>0$ with $\beta>\beta_c-\delta$ there is a step count $T(n)\le n^{3/2+o(1)}$ such that, with probability $1-o(1)$ over $G$, the random-cluster Glauber dynamics started from $X^+_0=E$ satisfies
--   $$\bigl\|X^+_{T(n)}-\pi^+_G\bigr\|_{TV}\le\varepsilon;$$
--   2. for every $0<\beta<\beta_c+\delta$ there is $T(n)\le n^{3/2+o(1)}$ such that, with probability $1-o(1)$, the dynamics from $X^-_0=\emptyset$ satisfies $\|X^-_{T(n)}-\pi^-_G\|_{TV}\le\varepsilon$;
--   3. there is one program for the unit-cost real RAM with fair coins such that for every $\beta>0$ there is $T_2(n)\le n^{2+o(1)}$ for which, with probability $1-o(1)$ over $G$, on input $n$, $d$, the adjacency lists of $G$, $\beta$ and $q$ the program halts within $T_2(n)$ steps on every sequence of coins and its output edge set has law within total variation $\varepsilon$ of $\pi_G$.
--
--   This is the paper's result for the random-cluster model with $q>2$, where the phase transition is first order and the ordered and disordered phases coexist at $\beta_c$: the phase guarantees hold uniformly in a neighbourhood of $\beta_c$, including $\beta_c$ itself, and the phase samplers combine into a sampler of the full law at every $\beta>0$.
--
--   **Formalization Note** The step counts and the program may depend on $d,q,\delta,K$; the step counts also on $\beta$. "With probability $1-o(1)$" is the published `WithHighProb d` over uniform simple $d$-regular graphs on $\{0,\dots,n-1\}$. The RAM is the published `SubsetConvFPRAS` machine with value oracles $0$; the sampled edge set is bitmap $0$, the edge $\{u,v\}$, $u<v$, numbered $un+v$.
--
--   Differences from the source:
--   - reading: "For any β > β_c − δ, (X⁺_t)_{t≥0} on G is within TV-distance ε from π⁺_G in t = Õ(n^{3/2}) steps" (and the same for β < β_c + δ) → each β is fixed before its step count T and before the whp event; reason: Õ hides constants that depend on β (the weak-Poincaré constant of Lemma 22 grows with e^{2B} for β ≤ B), so one step count for the unbounded range of β is not what is claimed; p.3 reads the paper's guarantees for fixed parameters, and the published goal (Theorem 1) is read the same way
--   - reading: "within TV-distance ε from π^±_G in t = Õ(n^{3/2}) steps" → TV distance ≤ n^{−K} at time T(n), for a function T of n with T(n) ≤ n^{3/2+ε′} eventually for every ε′ > 0; reason: the unrestricted chain eventually leaves its phase, so the claim is about a time T(n); Õ means up to an n^{o(1)} factor (p.2, p.5)
--   - reading: "there is an algorithm that, for any β > 0, outputs in time Õ(n²) an ε-sample from the full distribution π_G" → one admissible program, fixed before β, of the published unit-cost real RAM with fair coins (value oracles 0), on input (n, d, sorted adjacency lists, β, q); for each β > 0 a T₂ with T₂(n) ≤ n^{2+o(1)} such that whp it halts within T₂(n) steps on every coin tape and its output law (edge sets encoded as {un + v}) is within n^{−K} of π_G; reason: the paper names no machine model; the program comes before β as in the sentence, and the running time may depend on the fixed β as in the first reading
--   - encoding: β > β_c − δ (clause 1) → 0 < β ∧ β_c − δ < β; reason: the random-cluster model is defined for β > 0 (p.4); this only excludes parameters where π_G is undefined
--   - encoding: π_G ∝ (e^β − 1)^{|F|} q^{κ(F)}; RC Glauber dynamics; whp over G ∼ G_{n,d} → published rcLaw G (1 − e^{−β}) q and fkChain; WithHighProb d on Fin n; reason: p/(1 − p) = e^β − 1 at p = 1 − e^{−β}; the published uniform d-regular ensemble
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 2, p.4 (proved in §5 and §7)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_mm_mcmc
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_RandomCluster
import Definitions.Def_LowTempGlauber_IsNPowLittleO
import Definitions.Def_LowTempGlauber_Supplement_FinSampler
import Definitions.Def_LowTempGlauber_Supplement_RandomCluster

open Classical

namespace LowTempGlauber.Supplement

open MarkovMixing PottsRapidMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…7533d), Theorem 2, p.4 (proved in §5 and §7).

Fix an integer `d ≥ 3` and a real `q > 2`. There is `δ > 0` such that for every `K > 0`, whp over
`G ∼ G_{n,d}`, with `ε = n^{−K}` and `β_c = β_c(q, d)`:
1. for `β > β_c − δ`, the RC Glauber dynamics from `X⁺₀ = E` is within TV-distance `ε` of `π⁺_G` in
   `Õ(n^{3/2})` steps;
2. for `β < β_c + δ`, the RC Glauber dynamics from `X⁻₀ = ∅` is within `ε` of `π⁻_G` in `Õ(n^{3/2})`
   steps;
and there is an algorithm that, for any `β > 0`, outputs in time `Õ(n²)` an `ε`-sample from `π_G`.

**Formalization Note.**
* `δ` comes before `K` (existential); every `β` keeps `β > 0` (the model is defined for `β > 0`, p.4).
* Each `β` is fixed before its step count and the whp event (p.3: constants may depend on the
  parameters); the step counts `T(n) ≤ n^{3/2+o(1)}`, `T₂(n) ≤ n^{2+o(1)}` are functions of `n`.
* The chains are the unrestricted single-edge Glauber dynamics `fkChain G p q` of `π_G = rcB G β q`
  (`p = 1 − e^{−β}`); the targets are `π_G(· | E^±_G)`.
* The algorithm is one admissible program, fixed before `β` ("an algorithm that, for any `β > 0`"),
  of the published unit-cost real RAM with fair coins (value oracles `0`). Input `n, d`, the sorted
  adjacency lists, `β` (real cell 0) and `q` (real cell 1). It halts within `T₂(n)` steps on every coin
  tape, and the law of its output (bitmap `0`, the edge set under `edgeCode`) is within `n^{−K}` of
  `π_G` in TV. Whp is the published `WithHighProb d` (uniform simple `d`-regular graphs on `Fin n`). -/
theorem theorem_2 (d : ℕ) (hd : 3 ≤ d) (q : ℝ) (hq : 2 < q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 < K →
      (∀ β : ℝ, 0 < β → betaC q d - δ < β →
        ∃ T : ℕ → ℕ, LowTempGlauber.IsNPowLittleO T (3 / 2) ∧
          WithHighProb d (fun n G =>
            tvDist (rowDist (fkChain G (1 - Real.exp (-β)) q) (T n) (allIn G))
              (condLaw (rcB G β q) (IsRCPlus d q)) ≤ (n : ℝ) ^ (-K))) ∧
      (∀ β : ℝ, 0 < β → β < betaC q d + δ →
        ∃ T : ℕ → ℕ, LowTempGlauber.IsNPowLittleO T (3 / 2) ∧
          WithHighProb d (fun n G =>
            tvDist (rowDist (fkChain G (1 - Real.exp (-β)) q) (T n) (allOut G))
              (condLaw (rcB G β q) (IsRCMinus d q)) ≤ (n : ℝ) ^ (-K))) ∧
      ∃ P : SubsetConvFPRAS.Program, SubsetConvFPRAS.Admissible P ∧
        ∀ β : ℝ, 0 < β →
          ∃ T₂ : ℕ → ℕ, LowTempGlauber.IsNPowLittleO T₂ 2 ∧
            WithHighProb d (fun n G =>
              (∀ bits : Fin (T₂ n) → Bool,
                (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) (rcInit n d G β q)
                  (SubsetConvFPRAS.extendBits bits) (T₂ n)).output.isSome) ∧
              tvDist (outLaw P (rcInit n d G β q) (T₂ n)) (pushLaw (rcB G β q) (edgeCode G))
                ≤ (n : ℝ) ^ (-K)) := by sorry

end LowTempGlauber.Supplement
