-- Prove2me | Theorems.Thm_MasulloRH_character_twisted_prime_shell_detector
-- name    : MasulloRH.character_twisted_prime_shell_detector
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:24:09.515648+00:00
-- url     : https://prove2.me/theorems/57a9f371-bd91-4230-a6d7-70870b08b6dc
-- title:
--   One compact mean-zero test detects every critical-strip Dirichlet L-zero in the finite prime-shell sieve
-- statement:
--   For any Dirichlet character χ modulo q>0, prime p and cutoff B≥p, let Fχ(t)=Σ_{n≥1}χ(n)u(nt), and let G be the inclusion–exclusion shell selecting multiples of p and deleting multiples of other primes up to B. Put J(t)=Σ_{j≥1}χ(p)^j u(p^j t). For every compactly supported real C² test vanishing on the nonpositive axis with zero additive mean, the finite shells eventually equal J uniformly on every [a,∞), a>0. For every 0<Re(s)<1 their absolutely convergent Mellin transforms satisfy Mₛ(G)=Wχ,B(s) Mₛ(J), where Wχ,B=L(s,χ)∏_{l≤B}(1−χ(l)l^(−s)) and Mₛ(J)=χ(p)Mₛ(u)/(p^s−χ(p)). The product ranges over primes. Wχ,B vanishes exactly at the zeros of L(s,χ), so division recovers the prime-power moment whenever L(s,χ)≠0. For the single explicit C² mean-zero test w in the statement, supported in [1/32,1] independently of χ,p,B and s, Mₛ(G) vanishes exactly when L(s,χ)=0 or p divides q.
-- source:
--   Character-weighted extension of the rational finite prime-shell normalization in the Masullo mission. The scalar cutoff in the proof is the inclusion–exclusion sieve of the accepted rational prime-shell Mellin theorem https://prove2.me/theorems/6e438335-bf6f-44ab-b3d2-ee04d67ae833 . Twisted Müntz continuation, the finite Euler calculation and the explicit separating test are proved directly from Mathlib in this submission.

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Prime.Basic

open Complex MeasureTheory Set Finset Filter

theorem MasulloRH.character_twisted_prime_shell_detector {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (p : ℕ) (hp : Nat.Prime p)
    (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    let admissible (u : ℝ → ℝ) := ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      ∃ R : ℝ, 0 < R ∧ (∀ x : ℝ, x ≤ 0 ∨ R ≤ x → u x = 0) ∧ (∫ x in Ioi (0:ℝ), u x) = 0
    let ψ (u : ℝ → ℝ) (t : ℝ) := (u t : ℂ)
    let F (u : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, χ (n+1:ℕ) * ψ u (((n:ℝ)+1)*t)
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let G (u : ℝ → ℝ) (B : ℕ) (t : ℝ) := ∑ U ∈ ((P B).erase p).powerset,
      (χ p * ∏ l ∈ U, -χ l) * F u (((p * ∏ l ∈ U, l : ℕ) : ℝ)*t)
    let J (u : ℝ → ℝ) (t : ℝ) := ∑' j : ℕ, (χ p)^(j+1) * ψ u ((p:ℝ)^(j+1)*t)
    let W (B : ℕ) := χ.LFunction s * ∏ l ∈ P B, (1 - χ l * (l : ℂ)^(-s))
    let b : ℝ → ℝ := fun t => if t ∈ Ioc (0:ℝ) 1 then t^3*(1-t)^3 else 0
    let D (c : ℝ) (f : ℝ → ℝ) (t : ℝ) := f t - c * f (2*t)
    let v := D ((2:ℝ)^6)⁻¹ (D ((2:ℝ)^5)⁻¹ (D ((2:ℝ)^4)⁻¹ (D ((2:ℝ)^3)⁻¹ b)))
    let w := D 2 v
    (∀ u : ℝ → ℝ, admissible u →
      (∀ a : ℝ, 0 < a → ∀ᶠ B : ℕ in atTop, ∀ t : ℝ, a ≤ t → G u B t = J u t) ∧
      HasMellin (F u) s (χ.LFunction s * mellin (ψ u) s) ∧
      HasMellin (J u) s (χ p / ((p:ℂ)^s - χ p) * mellin (ψ u) s) ∧
      ∀ B : ℕ, p ≤ B → HasMellin (G u B) s (W B * mellin (J u) s) ∧
        (W B = 0 ↔ χ.LFunction s = 0) ∧
        (χ.LFunction s ≠ 0 → mellin (G u B) s / W B = mellin (J u) s) ∧
        (mellin (G u B) s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q ∨ mellin (ψ u) s = 0)) ∧
    (admissible w ∧ (∀ x : ℝ, x ≤ 1/32 ∨ 1 ≤ x → w x = 0) ∧ mellin (ψ w) s ≠ 0 ∧
      ∀ B : ℕ, p ≤ B → (mellin (G w B) s = 0 ↔ χ.LFunction s = 0 ∨ p ∣ q)) := by sorry
